/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Forcing and rebasing

Two arguments of Section 5 and Section 6 of the paper, stated free of geometry.

**Forcing** (Theorem 5.9, and the germ-forcing Lemma 6.9 in the same shape): a honeycomb is a
field of placed stars on the vertices of a connected graph — the `1`-skeleton — and when the star
at a vertex determines the star at every neighbour (the single-coset hypothesis, or the
germ-forcing hypothesis one shell further out), two such fields agreeing at one vertex agree
everywhere. The paper's proof is the induction along edge paths; here it is an induction along a
walk.

**Rebasing** (Lemma 6.7): the canonical fingerprint is the least encoding of the fingerprinted
set over the stabiliser `Stab±(S)`; a congruence between two honeycombs of the same species
normalises to an element of that stabiliser, so the two fingerprinted sets differ by a group
element and their least encodings coincide. The group-theoretic core: the minimum of a function
over a finite group orbit does not depend on the orbit representative.

## Main results

* `ConvexUniformHoneycombs.eq_on_walk_of_forcing`, `ConvexUniformHoneycombs.eq_of_forcing`
  (Theorem 5.9 / Lemma 6.9): a forced field is determined by its value at one vertex of a
  connected graph.
* `ConvexUniformHoneycombs.canonical_smul` (Lemma 6.7): the orbit minimum is invariant.
-/

namespace ConvexUniformHoneycombs

section Forcing

variable {V S : Type*} {G : SimpleGraph V} {f g : V → S}

/-- Along a walk, agreement propagates edge by edge when every edge forces. -/
theorem eq_on_walk_of_forcing (hforce : ∀ u v, G.Adj u v → f u = g u → f v = g v)
    {u v : V} (p : G.Walk u v) (hu : f u = g u) : f v = g v := by
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hforce _ _ hadj hu)

/-- **Forcing.** On a connected graph, two fields that force along every edge and agree at one
vertex are equal. In the paper: any two honeycombs carrying congruent stars, with the star at a
vertex forcing the stars at its neighbours, coincide once their stars at one vertex coincide —
the uniqueness half of Theorem 5.9, and the whole of Lemma 6.9 with germs for stars. -/
theorem eq_of_forcing (hG : G.Connected) (hforce : ∀ u v, G.Adj u v → f u = g u → f v = g v)
    (v₀ : V) (h₀ : f v₀ = g v₀) : f = g := by
  funext v
  obtain ⟨p⟩ := hG.preconnected v₀ v
  exact eq_on_walk_of_forcing hforce p h₀

end Forcing

section Rebasing

variable {G X E : Type*} [Group G] [Fintype G] [MulAction G X] [LinearOrder E]

/-- The canonical value of `x`: the least encoding over the orbit of `x` under the finite group
`G` — the canonical fingerprint, with `G = Stab±(S)` and `e` the sorted encoding. -/
def canonical (e : X → E) (x : X) : E :=
  Finset.univ.inf' Finset.univ_nonempty fun g : G => e (g • x)

/-- **Rebasing.** The canonical value is invariant under the group: `h • x` has the same orbit as
`x`. In the paper, a congruence `ψ` between two honeycombs fixing the base vertex and its placed
star lies in `Stab±(S)`, so the fingerprinted set of one is `ψ` applied to the other's, and their
canonical fingerprints agree. -/
theorem canonical_smul (e : X → E) (x : X) (h : G) :
    canonical (G := G) e (h • x) = canonical (G := G) e x := by
  unfold canonical
  apply le_antisymm
  · apply Finset.le_inf'
    intro g _
    calc (Finset.univ.inf' Finset.univ_nonempty fun g : G => e (g • (h • x)))
        ≤ e ((g * h⁻¹) • (h • x)) := Finset.inf'_le _ (Finset.mem_univ _)
      _ = e (g • x) := by rw [mul_smul, inv_smul_smul]
  · apply Finset.le_inf'
    intro g _
    calc (Finset.univ.inf' Finset.univ_nonempty fun g : G => e (g • x))
        ≤ e ((g * h) • x) := Finset.inf'_le _ (Finset.mem_univ _)
      _ = e (g • (h • x)) := by rw [mul_smul]

end Rebasing

end ConvexUniformHoneycombs
