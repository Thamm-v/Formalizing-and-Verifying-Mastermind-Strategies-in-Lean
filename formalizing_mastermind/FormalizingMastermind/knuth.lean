/-
Copyright (c) 2026 Nils Steuernagel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nils Steuernagel
-/
import FormalizingMastermind.the_game



/-!
# Formalization of Knuth's Algorithm
(Donald E. Knuth. The computer as Master Mind,
https://de.scribd.com/doc/36268017/Donald-Knuth-The-Computer-as-a-Mastermind-1977.)

This file implements the algorithm proposed by Knuth.
It generates feedback buckets, the worst case outcome of a guess, tie breaking
and choosing a guess.
-/

namespace Mastermind
namespace Knuth


/--
possible_secrets: all secrets that are still possible
turn: the guess and the feedback
Return all secrets that are possible with the turn given
-/
def bucket (candidates : Candidates) (turn : Turn46) : Candidates :=
  candidates.filter fun secret => evaluate46 secret turn.guess == turn.feedback


/--
- **guess**: the guess made
- **remaining_secrets**: the remaining secrets that have to be sorted into the buckets
- **bucket_sizes**: stores the amount of secrets that possible for each feedback, the
  index represents the feedback as a Nat.
- **worst_case**: the current worst case -> the size of the biggest bucket
- **upper_bound**: the previous best-worst-case bucket count;
  if the first guess had a worst case of 5, then the second guess only gets
  evaluated while its worst cas is ≤ 5. If the worst case for guess two gets
  bigger than 5 it is not the best-worst-case, guess 1 would keep that title.
-/
def worst_case_recursion
    (guess : StateNat46)
    (remaining_secrets : Candidates)
    (bucket_sizes : Array Nat)
    (worst_case : Nat)
    (upper_bound : Nat) : Option Nat :=
  match remaining_secrets with
  | [] => some worst_case
  | secret :: rest =>
      let index := feedback_index (evaluate46 secret guess)
      let new_bucket_size := bucket_sizes.getD index 0 + 1
      let worst_case := max worst_case new_bucket_size
      if upper_bound < worst_case then
        none
      else
        worst_case_recursion
          guess
          rest
          (bucket_sizes.modify index (fun count => count + 1))
          worst_case
          upper_bound

/--
returns the Optional size of the biggest feedback bucket, given a guess
-/
def worst_case_option
    (candidates : Candidates)
    (guess : StateNat46)
    (bound : Nat) : Option Nat :=
  worst_case_recursion
    guess
    candidates
    (Array.replicate FeedbackCount 0)
    0
    bound
/--
returns the Nat size of the biggest feedback bucket, given a guess
-/
def worst_case (candidates : Candidates) (guess : StateNat46) : Nat :=
  (worst_case_option candidates guess candidates.length ).getD 0



/--
The first code that gets put into a bucket to have a baseline for the upper bound
-/
def firstCode : StateNat46 :=
  ⟨
    0,
    by norm_num [StateNat46Count]
  ⟩

/--
decides if a candidate guess is valid and better then the current best guess
-/
@[inline] def wins_tie_break
    (candidates : Candidates)
    (candidate current_best : StateNat46) : Bool :=
  let candidate_valid := List.contains candidates candidate
  let current_best_valid := List.contains candidates current_best
  if candidate_valid == current_best_valid then
    decide (candidate.val < current_best.val)
  else
    candidate_valid

/--
returns the better guess of `\{previous_best_guess, guess\}` bucket size for the best guess
-/
def compare_guesses
    (candidates : Candidates)
    (best : StateNat46 × Nat)
    (guess : StateNat46) : StateNat46 × Nat :=
  match worst_case_option candidates guess best.2 with
  -- the worst bucket found for the guess was worse then the best-worse bucket
  | none => best
  | some worst_candidate =>
      if  decide (worst_candidate < best.2) ||
          wins_tie_break candidates guess best.1 then
        (guess, worst_candidate)
      else
        best

/--
returns the guess that minimizes the remaining secrets for the worst possible
feedback the guess could get
-/
def minimax_best_guess (candidates : Candidates) : StateNat46 :=
  match AllCodes with
  | [] => firstCode
  | first :: _ =>
      -- Every bucket has at most `candidates.length` secrets.
      (AllCodes.foldl
        (compare_guesses candidates)
        (first, candidates.length)).1


/--
returns the next guess given a candidates list

-> a history is not needed bc it would only be needed for calculating
the correct candidates set, if the candidates are already correct no changes
are needed
-/
def get_next_guess : Candidates → StateNat46
  | [secret] => secret
  | candidates => minimax_best_guess candidates

end Knuth
end Mastermind
