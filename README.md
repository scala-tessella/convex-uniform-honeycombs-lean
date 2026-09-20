# Lean 4 formalization for *The 28 convex uniform honeycombs: a completeness theorem*

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22858003.svg)](https://doi.org/10.5281/zenodo.22858003)

A Lean 4 + Mathlib formalization of the pen-and-paper mathematics of

> M. Càllisto, *The 28 convex uniform honeycombs: a completeness theorem* (2026).

That paper proves that every vertex-transitive face-to-face honeycomb of Euclidean 3-space by
unit-edge convex uniform polyhedra is one of the 28 convex uniform honeycombs. Its enumerations —
the 69 edge figures, the 34 vertex species, the 28 pattern classes and the completeness audit —
are finite certificates, replayed in exact arithmetic over ℚ(√2, √3) in the verification artifact,
and are **not** the target here. What remained human-checked is the mathematics around them: the
two-tier arithmetic that splits every angle equation into two integer equations, the closed-form
tail lemmas that exclude every antiprism at once, the exact identity behind the pentagon-family
edge figure, and the propagation, rebasing, seam and rigidity arguments of the pattern and
periodization sections. This repository formalizes those.

It is a companion to, and deliberately separate from, the verification artifact
[convex-uniform-honeycombs](https://github.com/scala-tessella/convex-uniform-honeycombs), and a
sibling of [minimal-uniformity-lean](https://github.com/scala-tessella/minimal-uniformity-lean).

## Contents

| file | contents |
| --- | --- |
| `ConvexUniformHoneycombs/TwoTier.lean` | `cos 2α = -1/3` for `α = arctan √2`; **Proposition 3.1**, `α` irrational in degrees by Niven's theorem, and the two-tier split of a lattice angle sum; the arithmetic of **Corollary 5.5** (the octet support `(8, 6)` is forced) |
| `ConvexUniformHoneycombs/Tails.lean` | **Lemmas A, B and E** of Section 4.2 from the closed-form antiprism dihedrals: `a₃q(q) > 90°`, `a₃₃(q) < 180°`, and `2 a₃q(q) + a₃₃(r) ≠ 360°` for all integers `q, r ≥ 4`, via the interleaving `2 sin(π/4q) < tan(π/2q) < 2 sin(π/(4q-2))` proved for every real `q ≥ 4`; the **tail corridors** of the uncapped corona fixpoint (Section 4.1): `a₃q` antitone and `a₃₃` monotone, so `a₃q(q) ∈ (π/2, a₃q(301)]` and `a₃₃(q) ∈ [a₃₃(301), π)` for `q ≥ 301`, and `π - 2π/p ∈ [π - 2π/501, π)` for `p ≥ 501` |
| `ConvexUniformHoneycombs/Separation.lean` | **Lemma 5.2**, the separation constant of the species search: the altitude of the tetrahedral corner — the vertex-to-opposite-side distance of the equilateral spherical triangle of side `60°` — is exactly `α = arctan √2`, proved on explicit coordinates of the corner figure (`sin²` of the altitude is `2/3 = sin² α`) |
| `ConvexUniformHoneycombs/Icosahedral.lean` | **Identity I2**: `θ₁ + θ₂ + θ₃ = 360°` from the three exact cosines, by the radical products and the injectivity of the cosine on `[0, π]` |
| `ConvexUniformHoneycombs/Forcing.lean` | **Theorem 5.9 / Lemma 6.9**, forcing along the edges of a connected graph; **Lemma 6.7**, the rebasing invariance of a canonical (orbit-minimal) fingerprint |
| `ConvexUniformHoneycombs/Periodization.lean` | **Remark 6.2**, the constants chain; the seam step (box coordinates congruent modulo the lattice differ by `-1`, `0` or `1`); **Lemma 6.5**, fundamental-box rigidity |

Everything is `sorry`-free and `native_decide`-free: each result depends only on `propext`,
`Classical.choice` and `Quot.sound`; the forcing theorem depends on `Quot.sound` alone and box
rigidity on `propext` and `Quot.sound`.

## Main statements

```lean
-- Proposition 3.1: α = arctan √2 is not a rational multiple of π
theorem alpha_ne_rat_mul_pi (q : ℚ) : alpha ≠ q * π

-- the two-tier split: zero total α-charge, rational parts adding up exactly
theorem two_tier_split {ι : Type*} (s : Finset ι) (a b : ι → ℤ) (c : ℚ)
    (h : ∑ i ∈ s, ((a i : ℝ) * (π / 12) + (b i : ℝ) * alpha) = c * π) :
    ∑ i ∈ s, b i = 0 ∧ ((∑ i ∈ s, a i : ℤ) : ℚ) = 12 * c

-- Lemma E: the antiprism-pair equation has no integer solution
theorem lemma_E (q r : ℕ) (hq : 4 ≤ q) (hr : 4 ≤ r) : 2 * a3q q + a33 r ≠ 2 * π

-- the interleaving, for every real q ≥ 4 (the paper's grid to q = 20000 is superseded)
theorem interleave_left  {q : ℝ} (hq : 4 ≤ q) : 2 * sin (π / (4 * q)) < tan (π / (2 * q))
theorem interleave_right {q : ℝ} (hq : 4 ≤ q) : tan (π / (2 * q)) < 2 * sin (π / (4 * q - 2))

-- the tail corridors of the uncapped corona fixpoint, for every real q ≥ 301 and p ≥ 501
theorem a3q_tail_corridor {q : ℝ} (hq : 301 ≤ q) : π / 2 < a3q q ∧ a3q q ≤ a3q 301
theorem a33_tail_corridor {q : ℝ} (hq : 301 ≤ q) : a33 301 ≤ a33 q ∧ a33 q < π
theorem prism_tail_corridor {p : ℝ} (hp : 501 ≤ p) :
    π - 2 * π / 501 ≤ π - 2 * π / p ∧ π - 2 * π / p < π

-- Lemma 5.2: the separation constant is the tetrahedral altitude, and it is α
theorem tet_altitude_sin_sq :
    (crossProduct tetA tetB ⬝ᵥ tetV) ^ 2 / (crossProduct tetA tetB ⬝ᵥ crossProduct tetA tetB) = 2 / 3
theorem tet_altitude : arcsin (√(2 / 3)) = alpha

-- Identity I2
theorem identity_I2 {θ₁ θ₂ θ₃ : ℝ}
    (h₁ : π / 2 < θ₁ ∧ θ₁ < π) (h₂ : π / 2 < θ₂ ∧ θ₂ < π) (h₃ : π / 2 < θ₃ ∧ θ₃ < π)
    (c₁ : cos θ₁ = -√(1 / 5)) (c₂ : cos θ₂ = -√r₂) (c₃ : cos θ₃ = -√r₃) :
    θ₁ + θ₂ + θ₃ = 2 * π

-- Theorem 5.9 / Lemma 6.9: a forced field on a connected graph is determined by one value
theorem eq_of_forcing (hG : G.Connected) (hforce : ∀ u v, G.Adj u v → f u = g u → f v = g v)
    (v₀ : V) (h₀ : f v₀ = g v₀) : f = g

-- Lemma 6.7: the canonical fingerprint is a congruence invariant
theorem canonical_smul (e : X → E) (x : X) (h : G) :
    canonical (G := G) e (h • x) = canonical (G := G) e x

-- Lemma 6.5: lattice-periodic honeycombs agreeing on a fundamental box are equal
theorem eq_of_periodic_of_agree_on_box {H₁ H₂ B : Set C}
    (h₁ : ∀ (l : L) (c : C), c ∈ H₁ → l +ᵥ c ∈ H₁) (h₂ : ∀ (l : L) (c : C), c ∈ H₂ → l +ᵥ c ∈ H₂)
    (hbox : ∀ c : C, ∃ l : L, l +ᵥ c ∈ B) (hagree : ∀ c ∈ B, c ∈ H₁ ↔ c ∈ H₂) : H₁ = H₂
```

## What is deliberately not formalized

The repository formalizes the *arguments*, not the searches, and states the geometric inputs as
hypotheses — the division of labour of its sibling. Specifically:

- **The enumerations** (the edge figures, the species table, the shell filter, the pattern
  classes, the audit). They are exact certificates in the artifact; re-deriving them in Lean would
  need `native_decide` and would replace a machine-checkable certificate with a weaker one.
- **The closed forms** of the antiprism dihedrals (the paper's equation (1)). The paper derives
  them from the coordinate model; here they are the definitions of `a3q` and `a33`.
- **The three cosines of Identity I2**, certified on exact `ℚ(√5)` models in the artifact; they
  enter as hypotheses, with the obtuseness of the angles.
- **The degree-1 spherical cover lemma** (Lemma 5.3) and the descriptor lemma, which need a
  covering-space degree and polyhedral geometry that Mathlib does not have.
- **The periodization theorem itself** (Theorem 6.1) beyond its arithmetic, seam and rigidity
  steps, and the coherence lemma (Lemma 6.6), whose geometric content is the periodization
  theorem's.

## Building

```bash
lake exe cache get
lake build
```

The toolchain is pinned: `lean-toolchain` fixes Lean 4 v4.33.1 and `lake-manifest.json` fixes the
Mathlib revision, so the build a reader reproduces is the build that was checked.

## Archival

Deposited on Zenodo as a supplement to the paper record. **Cite the version DOI of the release you
checked**, not the all-versions concept DOI
[10.5281/zenodo.22849888](https://doi.org/10.5281/zenodo.22849888) — the latter always resolves to
whatever is newest:

| Version | DOI |
|---|---|
| 0.2.0 | [10.5281/zenodo.22858003](https://doi.org/10.5281/zenodo.22858003) |
| 0.1.0 | [10.5281/zenodo.22849889](https://doi.org/10.5281/zenodo.22849889) |

Zenodo assigns a release's version DOI at the moment that release is published, so it cannot be present
in the tree that release archives: the `CITATION.cff` inside a deposit carries no version DOI. The version
DOI is recorded in this table, and in `CITATION.cff` on the main branch, in the first commit after the tag.

The companion computational artifact, deliberately separate from this formalization, is
[convex-uniform-honeycombs](https://github.com/scala-tessella/convex-uniform-honeycombs).
