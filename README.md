# Formalizing and Verifying Mastermind Strategies in Lean

Lean 4 code accompanying the bachelor's thesis 

**Formalizing and Verifying Mastermind Strategies in Lean** 

by **Nils Lennard Steuernagel**, 

Albert-Ludwigs-Universität Freiburg, 2026.

This project formalizes the game of Mastermind and verifies three strategies for finding a secret code: 
- exhaustive search,
- randomly guessing without repetition, 
- using a decision tree based on Knuth's minimax strategy.

The formalization covers codes, feedback, turns, histories, and game execution. The first two strategies are verified for arbitrary numbers of positions and colors. The decision tree is specialized for the standard game of **four** positions and **six** colors. This results in **1,296 possible secrets**.

**Start with [FormalizingMastermind.lean](formalizing_mastermind/FormalizingMastermind.lean)** for the central definitions and correctness theorems.


## Main results

The main file contains the following theorems:

| Theorem      | Result    |
| ------------ | --------- |
| `brute_force_correct`   | Enumerating all codes finds every secret for any game  `M(n,m)`.  |
| `brute_force_any_permutation_correct` | Searching any permutation of the complete state enumeration finds every secret.     |
| `KnuthsDecisionTree_correct`          | The stored tree finds all `1296` secrets within five guesses. |
| `knuth_game_won_within_five`    | Starting with an empty history, game execution using the stored tree wins within five guesses for every secret.           |


## Files

The main file is at the repository root. Supporting modules are in `FormalizingMastermind/`.

| File                                                                                                     | Purpose                                                                                                                                                      |
| -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| [FormalizingMastermind.lean](formalizing_mastermind/FormalizingMastermind.lean)                                                 | Main entry point. Includes the verification of the success of the naive search strategies and using the decision tree.             |
| [the_game.lean](formalizing_mastermind/FormalizingMastermind/the_game.lean)                                                     | General game model: functional and numeric states, feedback, turns, histories and game types. Also specialized to the standard game. |
| [knuth.lean](formalizing_mastermind/FormalizingMastermind/knuth.lean)                                                           | Knuth's proposed minimax algorithm. Includes feedback buckets, bucket sizes and  tie breaking.     |
| [decision_tree.lean](formalizing_mastermind/FormalizingMastermind/decision_tree.lean)    |  Includes Decision Tree structure, tree constructor using the minimax algorithm and next guess selection using the tree. |
| [generate_decision_tree_certificate.lean](formalizing_mastermind/FormalizingMastermind/generate_decision_tree_certificate.lean) | Includes the generator whose `main` function builds the tree and writes it as Lean source code. |
| [generated_decision_tree.lean](formalizing_mastermind/FormalizingMastermind/generated_decision_tree.lean)                       | Includes the tree called `KnuthsDecisionTree`. Is included in the repository but can be build using the main function of [generate_decision_tree_certificate.lean](formalizing_mastermind/FormalizingMastermind/generate_decision_tree_certificate.lean).     |

## Setup and verification

The project requires **Lean 4**, **Lake**, and **Mathlib**. Follow the [Lean installation instructions](https://lean-lang.org/install/) if needed. Use the Lean toolchain specified in `lean-toolchain` and the dependency versions recorded in the project's Lake configuration and `lake-manifest.json`.

From the repository root, go `cd` into the LEAN project, download the Mathlib build cache and build the main library. Downloading Mathlib can take some time.

```sh
cd formalizing_mastermind
lake exe cache get
lake build FormalizingMastermind
```

The build checks `FormalizingMastermind.lean` and its imported modules. This includes the proofs about the naive strategies and the stored decision tree. 
It is not needed to build the certificate but is possible.

## Regenerating the decision tree

`FormalizingMastermind/generated_decision_tree.lean` is already included in the repository. To re-generate it, run the generator's `main` function from the repository root:

```sh
lake build FormalizingMastermind.decision_tree
lake env lean --run FormalizingMastermind/generate_decision_tree_certificate.lean
```

This will **overwrite** the existing:

```sh
FormalizingMastermind/generated_decision_tree.lean
```


After regeneration, check the resulting certificate by rebuilding the main library:

```sh
lake build FormalizingMastermind
```

## License

The Lean source code is released under the Apache License 2.0. See [LICENSE](LICENSE).
