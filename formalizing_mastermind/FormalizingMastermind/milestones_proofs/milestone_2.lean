
/-
Copyright (c) 2026 Nils Steuernagel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nils Steuernagel
-/


import FormalizingMastermind.the_game
import FormalizingMastermind.milestones_proofs.milestone_1
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Find
import Mathlib.Data.List.Permutation

/-!
# Additional Theorems about the random search

This file includes additional theorems proving statements about searching
randomly without repetition.
-/

namespace MilestoneTwo


def brute_force_any_guesses {n m : Nat}
    (secret : Mastermind.StateNat n m)
    (guesses : List (Mastermind.StateNat n m)) :
    Option (Mastermind.StateNat n m) :=
--
  guesses.find? (fun guess => Mastermind.stateNat_eq guess secret)


/--
Brute force finds a result for every permutation of
`List.finRange (m ^ n)`.
-/
theorem brute_force_any_permutation_finds_secret {n m : Nat}
    (secret : Mastermind.StateNat n m)
    (rand_guesses : List (Mastermind.StateNat n m))
    (h_rand_guesses_perm_guesses : rand_guesses.Perm (List.finRange (m ^ n))) :
    brute_force_any_guesses secret rand_guesses = some secret := by
--
  obtain ⟨guess, h_guess⟩ :
      ∃ guess : Mastermind.StateNat n m,
      brute_force_any_guesses secret rand_guesses = some guess
      := by
    apply Option.isSome_iff_exists.mp
    unfold brute_force_any_guesses
    apply List.find?_isSome.mpr
--
    have h_secret_mem : secret ∈ rand_guesses := by
      apply h_rand_guesses_perm_guesses.mem_iff.mpr
      exact List.mem_finRange secret
--
    refine ⟨secret, h_secret_mem, ?_⟩
    simp [Mastermind.stateNat_eq]
--
  have h_guess_eq_secret : guess = secret := by
    have h_predicate := List.find?_some h_guess
    simpa [Mastermind.stateNat_eq] using h_predicate
--
  simpa [h_guess_eq_secret] using h_guess


theorem brute_force_any_permutation_finds_secret' {n m : Nat}
    (secret : Mastermind.StateNat n m)
    (rand_guesses : List (Mastermind.StateNat n m))
    (h_rand_guesses_perm_guesses : rand_guesses.Perm (List.finRange (m ^ n))) :
    brute_force_any_guesses secret rand_guesses = some secret := by
-- proving brute force returns some value
  obtain ⟨guess, h⟩ :
      ∃ guess, brute_force_any_guesses secret rand_guesses = some guess := by
    unfold brute_force_any_guesses
    apply Option.isSome_iff_exists.mp
    apply List.find?_isSome.mpr
    refine ⟨secret, h_rand_guesses_perm_guesses.mem_iff.mpr (List.mem_finRange secret), ?_⟩
    simp [Mastermind.stateNat_eq]
-- proving the found guess is the secret
  have h_guess_eq_secret : guess = secret := by
    unfold brute_force_any_guesses at h
    simpa [Mastermind.stateNat_eq] using List.find?_some h
  simpa [h_guess_eq_secret] using h





end MilestoneTwo
