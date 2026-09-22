/-
Copyright (c) 2026 Nils Steuernagel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nils Steuernagel
-/
import FormalizingMastermind.knuth
import Mathlib.Tactic.ToExpr

/-!
# Formalization of a Decision Tree based on Knuth's Algorithm

This file implements a tree structure together with a constructor based on the
minimax algorithm proposed by Knuth. It is used to solve Mastermind.

-/

namespace Mastermind



-- =============================================================================
-- # Building the Tree
-- =============================================================================

/--
Tree structure. Each node has a guess and branches based in the feedback its
guess receives. The branches lead to child nodes which should be guessed next.
-/
structure Tree where
  guess : StateNat46
  next_guesses : List (Feedback × Tree)

namespace Tree

/--
Returns a list of all still possible `secrets` depending on the `feedback`
given for the `guess`.
-/
def possible_children
    (possible_secrets : Candidates)
    (guess : StateNat46)
    : List (Feedback × Candidates) :=
  NotWinningFeedbacks.filterMap fun feedback =>
    let turn : Turn46 := ⟨guess, feedback⟩
    let candidates :=
      Knuth.bucket possible_secrets turn
    if candidates.isEmpty then
      none
    else
      some (feedback, candidates)

/--
builds a `tree` using for all possible `candidates`.
if it exceeds its `maximum depth` it returns none
-/
def build : Nat → Candidates → Option Tree
  | 0, _ =>
      none
  | _ + 1, [] =>
      none
  | _ + 1, [secret] =>
      some {
        guess := secret
        next_guesses := []
      }
  | remaining + 1, possible_secrets => do
      let guess := Knuth.get_next_guess possible_secrets
      let children_possible := possible_children possible_secrets guess
      let children ← children_possible.mapM fun branch => do
        let child ← build remaining branch.2
        pure (branch.1, child)
      pure {
        guess := guess
        next_guesses := children
      }

/--
Returns either complete decision tree or `none`.
A complete tree has at least every state in `AllCodes` and has a depth of at
most `5`.
-/
def start_build : Option Tree :=
  build 5 AllCodes


/--
Uses a history of previous `guesses` and their `feedback` to find the `guess`.
The the next `guess` is provided by the `Tree`.
If at any point the `History` and the `Tree` disagree, the function returns `none`.
If needed branches are missing the function returns `none`.
If the function finds the next `guess`, it is returned.
-/
def get_next_guess_using_history : History46 → Tree → Option StateNat46
  | [] , tree =>
      some tree.guess
  | turn :: rest_history , tree =>
      if turn.guess != tree.guess then
        none
      else
        match tree.next_guesses.find? (fun branch =>
          branch.1 == turn.feedback) with
        | none =>
            none
        | some (_, child) =>
            get_next_guess_using_history rest_history child
end Tree
end Mastermind
