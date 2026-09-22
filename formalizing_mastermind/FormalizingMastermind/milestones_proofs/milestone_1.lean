/-
Copyright (c) 2026 Nils Steuernagel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nils Steuernagel
-/

import FormalizingMastermind.the_game
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Find
import Mathlib.Data.List.Permutation

/-!
# Additional Theorems about the exhaustive search

This file includes additional theorems proving statements about the basic search.
-/



-- =============================================================================
-- Trying to brute force the correct guess
-- =============================================================================

namespace MilestoneOne
/--
Finding a correct guess using brute force by trying all possible values in
  [0, ..., m^n-1]
Starting at 0
-> The Code uses the Concept of Ms1
-/
def brute_force {n m : Nat}
    (secret : Mastermind.StateNat n m) :
    Option (Mastermind.StateNat n m) :=
--
  (List.finRange (m^n)).find? (fun guess => Mastermind.stateNat_eq guess secret)

/--
The bruteForce Funktion returns none if find? does not find a guess
for wich
  Mastermind.stateNatEq guess secret
returns True

If it can be proven that it always returns a some value, it shoes that
it always finds an answer
-/
theorem brute_force_always_type_some_forall_secret {n m : Nat} :
    ∀ secret : Mastermind.StateNat n m,
      ∃ guess : Mastermind.StateNat n m,
        brute_force secret = some guess := by
--
  intro secret
  apply Option.isSome_iff_exists.mp
--
  unfold brute_force
  apply List.find?_isSome.mpr
--
  refine
    ⟨
      secret,
      List.mem_finRange secret,
      ?_
    ⟩
--
  simp [Mastermind.stateNat_eq]

/--
The bruteForce Funktion returns none if find? does not find a guess
for wich
  Mastermind.stateNatEq guess secret
returns True

If it can be proven that it always returns a some value, it shoes that
it always finds an answer
-/
theorem brute_force_always_type_some {n m : Nat}
    (secret : Mastermind.StateNat n m) :
      ∃ guess : Mastermind.StateNat n m,
        brute_force secret = some guess := by
--
  apply Option.isSome_iff_exists.mp
--
  unfold brute_force
  apply List.find?_isSome.mpr
--
  refine
    ⟨
      secret,
      List.mem_finRange secret,
      ?_
    ⟩
--
  simp [Mastermind.stateNat_eq]


theorem brute_force_correct {n m : Nat}
    (secret : Mastermind.StateNat n m) :
    brute_force secret = some secret := by
-- proving brute force returns some value
  obtain ⟨guess, h⟩ : ∃ guess, brute_force secret = some guess := by
    unfold brute_force
    apply Option.isSome_iff_exists.mp
    apply List.find?_isSome.mpr
    refine ⟨secret, List.mem_finRange secret, ?_⟩
    simp [Mastermind.stateNat_eq]
-- proving the found guess is the secret
  have h_guess_eq_secret : guess = secret := by
    unfold brute_force at h
    simpa [Mastermind.stateNat_eq] using List.find?_some h
  simpa [h_guess_eq_secret] using h


/--
Proof that every possible secret can be found in the guesses List
-/
theorem every_secret_always_in_finNM {n m : Nat} :
    ∀ secret : Mastermind.StateNat n m,
      ∃ guess ∈ List.finRange (m ^ n),
        secret = guess := by
--
  intro secret
  refine
    ⟨
      secret,
      List.mem_finRange secret,
      rfl
    ⟩

theorem secret_always_in_finNM {n m : Nat}
    (secret : Mastermind.StateNat n m) :
    ∃ guess ∈ List.finRange (m ^ n),
      secret = guess := by
--
  refine
    ⟨
      secret,
      List.mem_finRange secret,
      rfl
    ⟩

end MilestoneOne
