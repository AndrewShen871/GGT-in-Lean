# GGT-in-Lean

Lean formalization of geometric group theory concepts (Cayley graphs, word metric, quasi-isometry) with Mathlib4.

## Status
- Code compiles with `lake build`.
- The project now includes scaffolding for automorphisms, quasi-isometry equivalence, and the Milnor-Schwarz direction.
- Several files still contain `sorry` placeholders and lightweight placeholder definitions; these are the main items still to be completed.

## Installation
1. Install Lean + Lake (if not installed yet)
   - See https://leanprover.github.io/lean4/doc/quickstart.html
   - Common commands: `elan default`, `lake --version`
2. Clone the repository and enter the project folder
   - `git clone https://github.com/AndrewShen871/GGT-in-Lean.git`
   - `cd GGT-in-Lean/cay`
3. Initialize dependencies and build
   - `lake env` → if mathlib is absent, this step automatically fetches mathlib
   - `lake build`
4. Run tests
   - `lake test` (if tests are provided; the project currently may not include a dedicated test suite)
   - To add a basic test, create a file under `Cay/` with a small asserted lemma and run `lake test`.

Notes:
- `lakefile.toml` already declares `mathlib` as a dependency at `v4.28.0-rc1`.
- After cloning, running the commands above works for all students and ensures consistent dependency versions.

## Module Structure

The codebase is organized by topic. In each topic, there is usually:

- a top-level entry file under `Cay/`
- one or more concrete implementation files under a same-named subdirectory

This means the top-level files such as `Cay/Wordlength.lean` and `Cay/QuasiIsometry.lean` are mainly aggregator files, while the real definitions and proofs live in the subfiles.

## File Hierarchy

Current structure:

```text
Cay/
	Basic.lean
	CayleyGraph.lean
	Automorphism.lean
	Automorphism/
		Basic.lean
		CayleyTheorem.lean
	MilnorSchwarz.lean
	MilnorSchwarz/
		Actions.lean
		OrbitMap.lean
		Main.lean
	Wordlength.lean
	Wordlength/
		Wordlength.lean
		WordlengthQv.lean
	Wordmetric.lean
	Wordmetric/
		Wordmetric.lean
	QuasiIsometry.lean
	QuasiIsometry/
		Basic.lean
		CayleyGraphs.lean
		Equivalence.lean
```

## Submodule Relations

### Cayley graph layer

- `Cay/CayleyGraph.lean`
	defines the Cayley graph itself, symmetry/generating predicates, path shifting, and connectivity results.
- This file is the base layer used by the word-length and word-metric developments.

### Word-length layer

- `Cay/Wordlength/Wordlength.lean`
	defines the standard word length and word distance using admissible words in the generating set.
- `Cay/Wordlength/WordlengthQv.lean`
	defines the Cayley-graph/path-length version `wordLength_qv` and `wordDist_qv`.
- `Cay/Wordlength.lean`
	is the aggregator for both files above:
	- `Cay.Wordlength.Wordlength`
	- `Cay.Wordlength.WordlengthQv`

So the relation is:

```text
Cay/Wordlength.lean
	-> Cay/Wordlength/Wordlength.lean
	-> Cay/Wordlength/WordlengthQv.lean
```

### Word-metric layer

- `Cay/Wordmetric/Wordmetric.lean`
	turns word distance into a real-valued metric and proves comparison lemmas between generating sets.
- `Cay/Wordmetric.lean`
	is the aggregator for `Cay/Wordmetric/Wordmetric.lean`.

So the relation is:

```text
Cay/Wordmetric.lean
	-> Cay/Wordmetric/Wordmetric.lean
```

### Quasi-isometry layer

- `Cay/QuasiIsometry/Basic.lean`
	contains the definition `IsQuasiIsometry` and the main basic construction used in this project.
- `Cay/QuasiIsometry/Equivalence.lean`
	is reserved for the equivalence-relation level statements for quasi-isometry.
- `Cay/QuasiIsometry/CayleyGraphs.lean`
	contains the skeleton statements saying that Cayley graph models coming from finite generating sets are quasi-isometric.
- `Cay/QuasiIsometry.lean`
	aggregates:
	- `Cay.QuasiIsometry.Basic`
	- `Cay.QuasiIsometry.CayleyGraphs`
	- `Cay.QuasiIsometry.Equivalence`

So the relation is:

```text
Cay/QuasiIsometry.lean
	-> Cay/QuasiIsometry/Basic.lean
	-> Cay/QuasiIsometry/Equivalence.lean
```

### Automorphism layer

- `Cay/Automorphism/Basic.lean`
	contains automorphism-related definitions and proofs.
- `Cay/Automorphism/CayleyTheorem.lean`
	contains the current skeleton statements toward Cayley's theorem and Cayley-graph automorphisms.
- `Cay/Automorphism.lean`
	is the aggregator for:
	- `Cay.Automorphism.Basic`
	- `Cay.Automorphism.CayleyTheorem`

So the relation is:

```text
Cay/Automorphism.lean
	-> Cay/Automorphism/Basic.lean
	-> Cay/Automorphism/CayleyTheorem.lean
```

### Milnor-Schwarz layer

- `Cay/MilnorSchwarz/Actions.lean`
	introduces placeholder notions of isometric, proper, cobounded, and geometric actions.
- `Cay/MilnorSchwarz/OrbitMap.lean`
	contains the orbit map and the coarse Lipschitz / expansive / surjective skeleton statements.
- `Cay/MilnorSchwarz/Main.lean`
	contains the Milnor-Schwarz lemma skeleton and its two quasi-isometry corollaries.
- `Cay/MilnorSchwarz.lean`
	aggregates all Milnor-Schwarz files.

So the relation is:

```text
Cay/MilnorSchwarz.lean
	-> Cay/MilnorSchwarz/Actions.lean
	-> Cay/MilnorSchwarz/OrbitMap.lean
	-> Cay/MilnorSchwarz/Main.lean
```

## Dependency Flow

At a high level, the mathematical dependency flow is:

```text
CayleyGraph
	-> Wordlength / WordlengthQv
	-> Wordmetric
	-> QuasiIsometry
	-> MilnorSchwarz
```

More concretely:

- `CayleyGraph` provides graph/path language.
- `Wordlength` and `WordlengthQv` use that language to define lengths/distances.
- `Wordmetric` packages the distance as a metric object and compares generating sets.
- `QuasiIsometry` uses the metric-space packaging to formulate coarse equivalence statements.
- `Automorphism` packages symmetry statements of the Cayley graph and prepares the route to Cayley's theorem.
- `MilnorSchwarz` is the current large-scale target direction, built on the quasi-isometry layer.

## Pending Work

The project builds, but the following pieces are still placeholders or proof skeletons.

### Quasi-isometry

- `Cay/QuasiIsometry/Equivalence.lean`
	- `quasiIsometric_refl`
	- `quasiIsometric_symm`
	- `quasiIsometric_trans`
- `Cay/QuasiIsometry/CayleyGraphs.lean`
	- `cayleyGraphs_quasiIsometric_of_finite_generating_sets`
	- `id_quasiIsometry_between_cayleyGraphs`
	- `cayleyGraph_quasiIsometryClass_independent_of_finite_generating_set`

### Automorphism / Cayley theorem

- `Cay/Automorphism/CayleyTheorem.lean`
	- `leftMul_cayleyGraphAut`
	- `leftRegular_to_cayleyPerm`
	- `cayley_theorem`
	- `labeledAut_determined_by_identity`

### Milnor-Schwarz

- `Cay/MilnorSchwarz/Actions.lean`
	- `ProperAction` and `CoboundedAction` are still placeholder definitions (`True`), so they need real mathematical formulations.
- `Cay/MilnorSchwarz/OrbitMap.lean`
	- `orbitMap_coarselyLipschitz`
	- `orbitMap_coarselyExpansive`
	- `orbitMap_coarselySurjective`
- `Cay/MilnorSchwarz/Main.lean`
	- `milnor_schwarz_lemma`
	- `group_quasiIsometric_space_of_geometric_action`
	- `spaces_quasiIsometric_of_common_geometric_action`

### Word-length comparison still worth adding

- `Cay/Wordlength/WordlengthQv.lean`
	- prove that the Cayley-graph definition `wordLength_qv` agrees with the standard `wordLength`
	- prove the corresponding equality for `wordDist_qv` and `wordDist`

These comparison theorems are not required for the file structure to compile, but they are an important bridge between the two word-length formalisms already present in the project.

## Import Convention

If you want the implementation file directly, import the file in the subdirectory.

Examples:

- `import Cay.Wordlength.Wordlength`
- `import Cay.Wordlength.WordlengthQv`
- `import Cay.QuasiIsometry.Basic`

If you want the whole topic, import the aggregator file.

Examples:

- `import Cay.Wordlength`
- `import Cay.Wordmetric`
- `import Cay.QuasiIsometry`
- `import Cay.Automorphism`
- `import Cay.MilnorSchwarz`
