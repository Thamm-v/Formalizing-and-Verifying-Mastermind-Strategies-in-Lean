/-
Copyright (c) 2026 Nils Steuernagel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nils Steuernagel
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.DeriveFintype
import Init.Omega

/-!
# Formalization of the game Mastermind

This file defines states, feedback, turns and game execution for Mastermind.
This includes a general Model of `n` positions and `m` colors and a specialized
version for `4` positions and `6` colors.
-/


open scoped BigOperators

namespace Mastermind

-- =============================================================================
-- Codes and their numeric representation
-- =============================================================================

/--
positional index of color in `[0, n - 1]`.
-/
abbrev Position (n : Nat) :=
  Fin n

/--
color index in `[0, m - 1]`.
-/
abbrev Color (m : Nat) :=
  Fin m

/--
guess (or secret) with `n` positions and `m` colors.
-/
abbrev State (n m : Nat) :=
  Position n → Color m

/--
state as a natural number in `[0, m^n - 1]`.
-/
abbrev StateNat (n m : Nat) := Fin (m ^ n)


/-- The standard equivalence between function-valued and numeric states. -/
def state_equivalent_to_StateNat (n m : Nat) :
    State n m ≃ StateNat n m :=
  finFunctionFinEquiv

/-- Encode a state numerically. -/
def to_StateNat {n m : Nat} (state : State n m) : StateNat n m :=
  state_equivalent_to_StateNat n m state

/-- Decode a numeric state. -/
def from_NatState {n m : Nat} (stateNat : StateNat n m) : State n m :=
  (state_equivalent_to_StateNat n m).symm stateNat

--  # Not needed ---------------------------------------------------------------
/-- The natural-number value of a state, written explicitly in base `m`. -/
def to_Nat {n m : Nat} (state : State n m) : Nat :=
  ∑ i : Fin n, (state i).val * m ^ i.val
--  # --------------------------------------------------------------------------


--  # Not needed ---------------------------------------------------------------
/-- Boolean equality for function-valued states. -/
def state_eq {n m : Nat} (guess secret : State n m) : Bool :=
  decide (guess = secret)
--  # --------------------------------------------------------------------------


/-- Boolean equality for numerically encoded states. -/
def stateNat_eq {n m : Nat} (guess secret : StateNat n m) : Bool :=
  decide (guess = secret)

-- =============================================================================
-- Evaluating a guess
-- =============================================================================

/--
Feedback for a guess.

- Black hits are count of exact Position and Color Pairs,
- White hits are color-only
-/
structure Result (pos : Nat) where
  black_hits : Fin (pos                  + 1)
  white_hits : Fin (pos - black_hits.val + 1)
deriving DecidableEq, Fintype



private def occurrences {pos col : Nat}
    (state : State pos col)
    (color : Color col) :
    Nat :=
  (
    (Finset.univ : Finset (Position pos)).filter
    (fun i => state i = color)
  ).card

/-- Number of positions where guess and secret are the same -/
def black_count {pos col : Nat}
    (guess secret : State pos col) : Nat :=
  ((Finset.univ : Finset (Position pos)).filter
    (fun i => guess i = secret i)).card

/-- Total number of color matches -/
def total_color_Hits {pos col : Nat}
    (guess secret : State pos col) : Nat :=
  ∑ color : Color col,
    min (occurrences guess color) (occurrences secret color)

/-- Number of color matches where position is not the same. -/
def white_count {pos col : Nat}
    (guess secret : State pos col) : Nat :=
  total_color_Hits guess secret - black_count guess secret




/-- Build feedback from black and white counts -/
def Result.from_counts {pos : Nat} (black white : Nat) : Result pos :=
  let black_fin : Fin (pos + 1) :=
    ⟨
      min black pos,
      Nat.lt_succ_of_le (min_le_right black pos)
    ⟩
--
  let white_fin : Fin (pos - black_fin.val + 1) :=
    ⟨
      min white (pos - black_fin.val),
      Nat.lt_succ_of_le (min_le_right white (pos - black_fin.val))
    ⟩
--
  ⟨black_fin, white_fin⟩

--  # Not needed ---------------------------------------------------------------
/-- Feedback as a pair of Nat numbers -/
def Result.as_tuple {pos : Nat} (result : Result pos) : Nat × Nat :=
  (result.black_hits.val, result.white_hits.val)
--  # --------------------------------------------------------------------------


/-- Returns feedback for a guess given a secret. -/
def evaluate {pos col : Nat}
    (guess secret : State pos col) :
    Result pos :=
  --
  let black_hits := black_count guess secret
  let white_hits := white_count guess secret
  --
  Result.from_counts (pos := pos) black_hits white_hits

/--
decides if the game is won and returns the bool decision
-/
def game_won {pos col : Nat}
    (guess secret : State pos col) :
    Bool :=
  decide ((evaluate guess secret).black_hits.val = pos)

theorem from_counts_preserves_counts
    {pos black white : Nat}
    (hblack : black ≤ pos)
    (hwhite : white ≤ pos - black) :
    (Result.from_counts (pos := pos) black white).black_hits.val = black ∧
    (Result.from_counts (pos := pos) black white).white_hits.val = white := by
  constructor
  · change min black pos = black
    exact Nat.min_eq_left hblack
  · change min white (pos - min black pos) = white
    rw [Nat.min_eq_left hblack]
    exact Nat.min_eq_left hwhite

-- =============================================================================
-- Turns, histories and the game
-- =============================================================================

/-- A turn including a guess and its feedback. -/
structure Turn (pos col : Nat) where
  guess : State pos col
  feedback : Result pos
deriving DecidableEq

/-- Construct the uniquely correct turn for a secret and guess. -/
def make_turn {pos col : Nat} (secret guess : State pos col) :
    Turn pos col := ⟨guess, evaluate guess secret ⟩

namespace Turn
/-- Decides if a turn is winning. -/
def is_winning {pos col : Nat} (turn : Turn pos col) :
    Bool :=
  decide (turn.feedback.black_hits.val = pos)
end Turn

/-- The record of all turns. -/
abbrev History (pos col : Nat) :=
  List (Turn pos col)

namespace History

/-- Does the history contain a winning turn? -/
def has_winning_turn {pos col : Nat} (history : History pos col) :
    Bool :=
  history.any Turn.is_winning

/-- Propositional of `has_winning_turn`. -/
abbrev has_won {pos col : Nat} (history : History pos col) :
    Prop :=
  history.has_winning_turn = true

end History

inductive legal_history {pos col : Nat}
    (secret : State pos col) : History pos col → Prop
  | nil : legal_history secret []
  | snoc {history : History pos col}
      (history_legal : legal_history secret history)
      (ongoing : ¬ history.has_won)
      (guess : State pos col) :
      legal_history secret (history ++ [make_turn secret guess])


structure Game (pos col : Nat) where
  secret : State pos col
  history : History pos col


def Game.initial {pos col : Nat}
    (secret : State pos col) : Game pos col :=
  ⟨
    secret,
    [],
  ⟩

def Game.is_end_of_game {pos col : Nat} (state : Game pos col) :
    Prop :=
  state.history.has_won



-- =============================================================================
-- If Positions <- 4 and Colors <- 6
-- =============================================================================

/-- Number positions in the standard game `:= 4`. -/
abbrev STANDART_POSITIONS : Nat := 4
/-- Number colors in the standard game `:= 6`. -/
abbrev STANDART_COLORS : Nat := 6

/-- Number of codes in the standard game `:= 6^4 = 1296`. -/
def StateNat46Count : Nat := STANDART_COLORS ^ STANDART_POSITIONS
/-- The StateNat for the standard game `:= StateNat (6^4)`. -/
abbrev StateNat46 := StateNat STANDART_POSITIONS STANDART_COLORS
/-- The Result for the standard game `:= Result 4`. -/
abbrev Feedback := Result STANDART_POSITIONS
/-- A List of possible StateNat for the standard game `:= List (StateNat (6^4))`. -/
abbrev Candidates := List StateNat46
/--
A List of all possible StateNat for the standard game `:= [0, 1, ... , 6^4 -1]`.
-/
def AllCodes : Candidates := List.finRange StateNat46Count

/-- Reduce any natural number to a standard-game code. -/
def to_StateNat46 (value : Nat) : StateNat46 :=
  ⟨
    value % StateNat46Count,
    Nat.mod_lt _ (by norm_num [StateNat46Count])
  ⟩

/-- Score two numerically encoded standard-game codes. -/
def evaluate46 (secret guess : StateNat46) : Feedback :=
  evaluate (from_NatState guess) (from_NatState secret)











/-- A turn including a guess and its feedback. -/
structure Turn46 where
  guess : StateNat46
  feedback : Feedback
deriving DecidableEq

/-- Construct the uniquely correct turn for a secret and guess. -/
def make_turn46 (guess secret : StateNat46) : Turn46 :=
  ⟨guess, evaluate46 guess secret⟩


namespace Turn46
/-- Decides if a turn is winning. -/
def is_winning (turn : Turn46) :
    Bool :=
  decide (turn.feedback.black_hits.val = 4)

end Turn46



/-- The record of all turns. -/
abbrev History46 :=
  List (Turn46)

namespace History46

/-- Does the history contain a winning turn? -/
def has_winning_turn (history : History46) :
    Bool :=
  history.any Turn46.is_winning

/-- Propositional of `has_winning_turn`. -/
abbrev has_won (history46 : History46) :
    Prop :=
  history46.has_winning_turn = true

end History46



structure Game46 where
  secret : StateNat46
  history : History46
namespace Game46

def initial (secret : StateNat46) :
    Game46 :=
  {
    secret := secret,
    history := []
  }

def make_turn (guess : StateNat46) (game46 : Game46) : Game46 :=
  let turn := make_turn46 guess game46.secret
  {
    secret := game46.secret,
    history := game46.history.concat turn
  }

def is_end_of_game (game46 : Game46) :
    Prop :=
  game46.history.has_won

end Game46





/-- All valid feedback values for the standard game. -/
def Feedbacks : List Feedback :=
  [
    Result.from_counts 0 0, -- index  0
    Result.from_counts 0 1, -- index  1
    Result.from_counts 0 2, -- index  2
    Result.from_counts 0 3, -- index  3
    Result.from_counts 0 4, -- index  4
    Result.from_counts 1 0, -- index  5
    Result.from_counts 1 1, -- index  6
    Result.from_counts 1 2, -- index  7
    Result.from_counts 1 3, -- index  8
    Result.from_counts 2 0, -- index  9
    Result.from_counts 2 1, -- index 10
    Result.from_counts 2 2, -- index 11
    Result.from_counts 3 0, -- index 12
    Result.from_counts 3 1, -- index 12 -> unreachable
    Result.from_counts 4 0  -- index 13
  ]

/--
Calculates a Nat number of a feedback
The number is also the position in the Feedbacks list

(13 is the index for the unreachable feedback `(3,1)` -> it should never happen)
-/
@[inline] def feedback_index (result : Feedback) : Nat :=
  match result.black_hits.val with
  | 0 => result.white_hits.val
  | 1 => 5 + result.white_hits.val
  | 2 => 9 + result.white_hits.val
  | 3 => 12 + result.white_hits.val --
  | _ => 14


/-- Number of feedback buckets in the standard game. -/
def FeedbackCount : Nat := Feedbacks.length

/-- The winning feedback value: four black hits and no white hits. -/
def WinningFeedback : Feedback := Result.from_counts STANDART_POSITIONS 0

def NotWinningFeedbacks : List Feedback :=
  Feedbacks.filter fun result => !(result == WinningFeedback)








/--
conversion between numeric and functional state returns the same object
-/
@[simp] theorem from_to_StateNat {n m : Nat} (state : State n m) :
    from_NatState (to_StateNat state) = state := by
  exact (state_equivalent_to_StateNat n m).symm_apply_apply state

/--
conversion between numeric and functional state returns the same object
-/
@[simp] theorem to_from_StateNat {n m : Nat} (state : StateNat n m) :
    to_StateNat (from_NatState state) = state := by
  exact (state_equivalent_to_StateNat n m).apply_symm_apply state

/--
Prove that to_StateNat is injective
-/
theorem injection_state_stateNat {n m : Nat} :
    Function.Injective (fun state : State n m => to_StateNat state) := by
  exact (state_equivalent_to_StateNat n m).injective

/--
Prove that to_StateNat is surjective
-/
theorem surjection_state_stateNat {n m : Nat} :
    Function.Surjective (fun state : State n m => to_StateNat state) := by
  exact (state_equivalent_to_StateNat n m).surjective

/--
Prove that to_StateNat is bijective
-/
theorem bijection_state_stateNat {n m : Nat} :
    Function.Bijective (fun state : State n m => to_StateNat state) := by
  exact (state_equivalent_to_StateNat n m).bijective

/--
Prove that from_counts does not change the counts
-/
theorem from_counts_is_as_tuple {pos black white : Nat}
    (h_black_le_pos : black ≤ pos)
    (h_white_le_pos_sub_black : white ≤ pos - black) :
    Result.as_tuple (Result.from_counts (pos := pos) black white) =
      (black, white) := by
  rw [Result.as_tuple, Result.from_counts]
  simp [Nat.min_eq_left h_black_le_pos,
    Nat.min_eq_left h_white_le_pos_sub_black]
end Mastermind
