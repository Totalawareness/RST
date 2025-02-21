# Relational Syntax Theory (RST) - Coq Formalization

This repository contains the Coq formalization of the foundational framework of Relational Syntax Theory (RST), as presented in the paper:

> Yves Brodsky. "The Non-Duplication Theorem in Relational Syntax Theory: A Foundation for Discrete Mathematical Physics."

**Abstract (from the paper):**

> We establish a rigorous foundation for Relational Syntax Theory (RST), a novel mathematical framework for discrete physics based on purely syntactic principles. Central to RST is the *Non-Duplication Theorem*, which states that any derivable expression contains at most one occurrence of a distinguished symbol ⋆. We provide a complete mathematical formalization of derivable expressions over an admissible alphabet equipped with concatenation and enclosure operators. The proof of the Non-Duplication Theorem proceeds by structural induction and is verified using the Coq proof assistant.
>
> Our main contributions include: (1) a formal definition of derivability with explicit constraints on symbol occurrence, (2) an algorithmic Boolean parser proven equivalent to the inductive definition, (3) a rigorous proof of the Non-Duplication Theorem, and (4) the construction of a syntactic topology with a boundary operator satisfying ∂² = NIL. This establishes RST as a well-defined mathematical structure suitable for discrete formulations of physical theories.
>
> The framework's consistency is demonstrated through machine-verified proofs, and its falsifiability is established through an explicit criterion based on the Non-Duplication Theorem. These results provide a foundation for developing discrete analogues of conservation laws and symmetries without requiring pre-existing notions of space, time, or continuous parameters.

## Repository Contents

*   **`rst.v`:** The Coq source code containing the formal definitions, theorems, and proofs for the foundational framework of RST. This includes:
    *   The definition of the `Expr` type (representing expressions).
    *   The `occStar` function (counting occurrences of the distinguished symbol `⋆`).
    *   The `Derivable` predicate (defining the rules for constructing valid expressions).
    *   The `isDerivable` function (a Boolean parser for checking derivability).
    *   The proof of the Non-Duplication Theorem (`no_dup_star`).
    *   The proof of the equivalence between `Derivable` and `isDerivable`.
    *   The falsifiability lemma (`falsifiabilite_locale`).
    *   The exhaustive closure lemma (`closure_exhaustive`)

*   **`LICENSE`:** The MIT License file, specifying the terms of use for this code.

*   **`README.md`:** This file, providing an overview of the project and instructions.

## Requirements

To compile and interact with the Coq code, you will need:

*   **Coq:** Version 8.13 or later (tested with 8.16.1).  Installation instructions can be found on the official Coq website: [https://coq.inria.fr/download](https://coq.inria.fr/download)
*   **Coq Libraries:** The following standard Coq libraries are used:
    *   `Coq.Init.Nat` (Natural numbers)
    *   `Coq.Bool.Bool` (Booleans)
    *   `Coq.Arith.PeanoNat` (Peano arithmetic)
    *   `Lia` (Linear integer arithmetic)  These libraries are usually included with a standard Coq installation.

## Compilation and Usage

You can compile the code and interact with it using one of the following methods:

**1. CoqIDE (Graphical Interface):**

   *   Open the `rst.v` file in CoqIDE.
   *   Use the "Compile" menu and select "Compile Buffer".
   *   You can step through the proofs using the navigation commands in CoqIDE (forward, backward, go to end).

**2. Visual Studio Code (VS Code) with VsCoq Extension (Recommended):**

   *   Install VS Code: [https://code.visualstudio.com/](https://code.visualstudio.com/)
   *   Install the VsCoq extension (search for "VsCoq Platform" in the Extensions tab).
   *   Open the `rst.v` file in VS Code. VsCoq will automatically provide syntax highlighting, error checking, and interactive proof development features.

**3. Command Line (Terminal):**

   *   Open a terminal or command prompt.
   *   Navigate to the directory containing the `rst.v` file.
   *   Run the command: `coqc rst.v`
   *   This will generate a compiled file `rst.vo`.

**Key Definitions and Theorems:**

*   **`Expr`:** The inductive type representing expressions in RST.
*   **`occStar (e : Expr) : nat`:**  Returns the number of occurrences of the distinguished symbol `STAR` (⋆) in the expression `e`.
*   **`Derivable (e : Expr) : Prop`:**  A predicate that holds if and only if the expression `e` is derivable according to the rules of RST.
*   **`isDerivable (e : Expr) : bool`:**  A Boolean function (parser) that returns `true` if and only if the expression `e` is derivable.
*   **`no_dup_star : forall e, Derivable e -> occStar e <= 1`:** The Non-Duplication Theorem.
*   **`parse_implies_derivable : forall e, isDerivable e = true -> Derivable e`:**  The parser is sound.
*   **`derivable_implies_parse : forall e, Derivable e -> isDerivable e = true`:** The parser is complete.
* **`falsifiabilite_locale : forall e, occStar e >= 2 -> ~ Derivable e`:** The Falsifiability Criterion.

## License

This code is released under the MIT License. See the `LICENSE` file for details.

## Author

Yves Brodsky
