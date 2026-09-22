/-
Copyright (c) 2026 Nils Steuernagel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nils Steuernagel
-/


import FormalizingMastermind.the_game
import FormalizingMastermind.knuth
import FormalizingMastermind.decision_tree
import FormalizingMastermind.generated_decision_tree


/-!
# Verification of naive strategies and Knuth's strategy

This file is the main file for this project.
It holds the central theorems about the overarching thesis.

The proofs establish three strategies (and therefore the three milestones):
- exhaustive search finds every secret
- and random search finds every secret for any order
- the decision tree, based on Knuth finds every secret within `5` guesses
-/

-- =============================================================================
-- ## Milestone 1
-- =============================================================================

/--
Search the complete enumeration of all States.
If it finds the `secret`, it returns its guess: `some guess`,
If it does not find the `secret`, it returns `none`.
-/
def brute_force {n m : Nat}
    (secret : Mastermind.StateNat n m) :
    Option (Mastermind.StateNat n m) :=
--
  (List.finRange (m^n)).find? (fun guess => Mastermind.stateNat_eq guess secret)

/--
Prove that every possible `secret` is found using the `brute_force` function
and that the function returns `some secret` for every possible `secret`.
-/
theorem brute_force_correct {n m : Nat}
    (secret : Mastermind.StateNat n m) :
    brute_force secret = some secret := by
  -- show that the search returns a value.
  obtain ⟨guess, h⟩ : ∃ guess, brute_force secret = some guess := by
    unfold brute_force
    apply Option.isSome_iff_exists.mp
    apply List.find?_isSome.mpr
    refine ⟨secret, List.mem_finRange secret, ?_⟩
    simp [Mastermind.stateNat_eq]
  -- show that the returned guess is the secret.
  have h_guess_eq_secret : guess = secret := by
    unfold brute_force at h
    simpa [Mastermind.stateNat_eq] using List.find?_some h
  simpa [h_guess_eq_secret] using h




-- =============================================================================
-- ## Milestone 2
-- =============================================================================

/--
Search a list of all States.
If it finds the `secret`, it returns its guess: `some guess`,
If it does not find the `secret`, it returns `none`.
-/
def brute_force_any_guesses {n m : Nat}
    (secret : Mastermind.StateNat n m)
    (guesses : List (Mastermind.StateNat n m)) :
    Option (Mastermind.StateNat n m) :=
--
  guesses.find? (fun guess => Mastermind.stateNat_eq guess secret)

/--
Prove that every possible `secret` is found using `brute_force_any_guesses`,
iff the list of guesses is a permutation of the complete enumeration.
It is also proven, that the brute force function returns `some secret`
for every possible `secret`.
-/
theorem brute_force_any_permutation_correct {n m : Nat}
    (secret : Mastermind.StateNat n m)
    (rand_guesses : List (Mastermind.StateNat n m))
    (h_guesses_perm : rand_guesses.Perm (List.finRange (m ^ n))) :
    brute_force_any_guesses secret rand_guesses = some secret := by
  -- show that the search returns a value.
  obtain ⟨guess, h⟩ :
      ∃ guess, brute_force_any_guesses secret rand_guesses = some guess := by
    unfold brute_force_any_guesses
    apply Option.isSome_iff_exists.mp
    apply List.find?_isSome.mpr
    refine ⟨secret, h_guesses_perm.mem_iff.mpr (List.mem_finRange secret), ?_⟩
    simp [Mastermind.stateNat_eq]
  -- show that the returned guess is the secret.
  have h_guess_eq_secret : guess = secret := by
    unfold brute_force_any_guesses at h
    simpa [Mastermind.stateNat_eq] using List.find?_some h
  simpa [h_guess_eq_secret] using h


-- =============================================================================
-- ## Milestone 3
-- =============================================================================

/-- Checks if a `secret` can be found using the a `Decision Tree` -/
def Tree.finds_secret (secret : Mastermind.StateNat46) : Nat → Mastermind.Tree → Bool
  | 0, _ => false
  | remaining + 1, tree =>
      if tree.guess == secret then
        true
      else
        let feedback := Mastermind.evaluate46 secret tree.guess
        match tree.next_guesses.find? (fun branch =>
          branch.1 == feedback) with
        | none => false
        | some (_, child) => finds_secret secret remaining child

/--
Checks if all `secrets` can be found using a `Decision Tree`
in at most `maximum_guesses`
-/
def Tree.finds_all_secrets_in (maximum_guesses : Nat) (tree : Mastermind.Tree) : Bool :=
  Mastermind.AllCodes.all fun secret => finds_secret secret maximum_guesses tree

/-- Proof that all 1,296 possible secrets are found using the secret. -/
theorem KnuthsDecisionTree_correct :
    Tree.finds_all_secrets_in 5 Mastermind.Knuth.KnuthsDecisionTree = true ∧
    Tree.finds_all_secrets_in 4 Mastermind.Knuth.KnuthsDecisionTree = false := by
  decide +kernel



def turn_codemaker (game : Mastermind.Game46) (guess : Mastermind.StateNat46)
    : Mastermind.Game46 :=
  game.make_turn guess

def turn_codebreaker (history : Mastermind.History46) (tree : Mastermind.Tree)
    : Option Mastermind.StateNat46 :=
  Mastermind.Tree.get_next_guess_using_history history tree


def play_game
    (game : Mastermind.Game46) (tree : Mastermind.Tree)
    : Nat → Bool
  | 0 => false
  | remaining + 1 =>
    let guess := turn_codebreaker game.history tree
    match guess with
    | none => false
    | some guess =>
      let game := turn_codemaker game guess
      if game.history.has_winning_turn then
        true
      else
        play_game game tree remaining

set_option maxRecDepth 10000 in
-- set_option maxHeartbeats 0 in
theorem knuth_game_won_within_five :
    ∀ secret: Mastermind.StateNat46,
    play_game
      ⟨secret, []⟩ -- empty history
      Mastermind.Knuth.KnuthsDecisionTree 5 = true
      := by
  decide +kernel
