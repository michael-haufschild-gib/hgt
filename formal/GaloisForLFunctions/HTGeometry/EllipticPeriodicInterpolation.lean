import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Lattice-periodic interpolation at finitely many points

The capacity constructions on a product `E × ℂ*` need, for finitely many points of `E` that are
pairwise distinct, lattice-periodic functions taking prescribed values at them.  This file supplies
them, with no elliptic structure theory: neither the argument principle, nor the order of `℘`, nor
the structure theorem for the field of elliptic functions is used.

The whole construction rests on one fact already in mathlib: `℘` is discontinuous exactly at the
lattice.  If two points `x`, `y` were inseparable by every translate `z ↦ ℘(z − c)`, then `℘` would
be invariant under the translation by `y − x`, which is not in the lattice; but `℘` is continuous
there and discontinuous at `0`, and translation-invariance transports continuity from one to the
other.  So the translates separate points modulo the lattice, and a Lagrange product in the
separating translates produces the interpolating family.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {L : PeriodPair}

/-! ### Continuity off the lattice -/

/-- `℘` is continuous at every point off the lattice. -/
theorem continuousAt_weierstrassP {x : ℂ} (hx : x ∉ L.lattice) :
    ContinuousAt L.weierstrassP x := by
  have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  exact (L.differentiableOn_weierstrassP.differentiableAt (hopen.mem_nhds hx)).continuousAt

/-! ### Translates of `℘` separate points modulo the lattice -/

/-- **The translates of `℘` separate points modulo the lattice.**  If they did not separate `x` from
`y`, then `℘` would be invariant under translation by `y − x`; since `y − x` is off the lattice, `℘`
is continuous there, and the invariance would carry that continuity to the lattice point `0`, where
`℘` is discontinuous. -/
theorem exists_weierstrassP_translate_ne {x y : ℂ} (h : x - y ∉ L.lattice) :
    ∃ c : ℂ, L.weierstrassP (x - c) ≠ L.weierstrassP (y - c) := by
  by_contra hcon
  push Not at hcon
  have hdlat : y - x ∉ L.lattice := by
    intro hmem
    refine h ?_
    have := Submodule.neg_mem _ hmem
    simpa using this
  have hper : ∀ w : ℂ, L.weierstrassP w = L.weierstrassP (w + (y - x)) := by
    intro w
    have hw := hcon (x - w)
    have h1 : x - (x - w) = w := by ring
    have h2 : y - (x - w) = w + (y - x) := by ring
    rw [h1, h2] at hw
    exact hw
  have hcontd : ContinuousAt L.weierstrassP (y - x) := continuousAt_weierstrassP hdlat
  have hinner : ContinuousAt (fun w : ℂ => w + (y - x)) 0 := (continuous_add_const _).continuousAt
  have hshift : ContinuousAt (fun w : ℂ => L.weierstrassP (w + (y - x))) 0 := by
    simpa [Function.comp_def] using hcontd.comp_of_eq hinner (by simp)
  have hzero : ContinuousAt L.weierstrassP 0 := by
    have hfun : L.weierstrassP = fun w : ℂ => L.weierstrassP (w + (y - x)) := funext hper
    rw [hfun]
    exact hshift
  exact L.not_continuousAt_weierstrassP 0 (Submodule.zero_mem _) hzero

/-! ### The interpolating family -/

/-- The Lagrange product in translates of `℘` chosen to separate the interpolation points. -/
def latticeLagrange (L : PeriodPair) {n : ℕ} (p : Fin n → ℂ) (c : Fin n → Fin n → ℂ)
    (j : Fin n) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j,
    (L.weierstrassP (z - c j i) - L.weierstrassP (p i - c j i)) /
      (L.weierstrassP (p j - c j i) - L.weierstrassP (p i - c j i))

/-- The Lagrange product is lattice-periodic: every factor is a translate of `℘`. -/
theorem latticeLagrange_add_lattice {n : ℕ} (p : Fin n → ℂ) (c : Fin n → Fin n → ℂ)
    (j : Fin n) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    latticeLagrange L p c j (z + l) = latticeLagrange L p c j z := by
  rw [latticeLagrange, latticeLagrange]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hshift : z + l - c j i = (z - c j i) + ((⟨l, hl⟩ : L.lattice) : ℂ) := by
    ring
  rw [hshift, L.weierstrassP_add_coe]

/-- At its own node the Lagrange product is `1`, at every other node it is `0`. -/
theorem latticeLagrange_apply {n : ℕ} (p : Fin n → ℂ) (c : Fin n → Fin n → ℂ)
    (hc : ∀ j i : Fin n, i ≠ j →
      L.weierstrassP (p j - c j i) ≠ L.weierstrassP (p i - c j i)) (i j : Fin n) :
    latticeLagrange L p c j (p i) = if i = j then 1 else 0 := by
  classical
  rw [latticeLagrange]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun k hk => ?_
    have hkj : k ≠ i := (Finset.mem_erase.mp hk).1
    exact div_self (sub_ne_zero.mpr (hc i k hkj))
  · rw [if_neg hij]
    refine Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) ?_
    rw [sub_self, zero_div]

/-- **Lattice-periodic interpolation.**  Finitely many points, pairwise distinct modulo the lattice,
carry a family of lattice-periodic functions with `f j (p i) = δ_{ij}`. -/
theorem exists_latticePeriodic_interpolation {n : ℕ} (p : Fin n → ℂ)
    (hp : ∀ i j : Fin n, i ≠ j → p i - p j ∉ L.lattice) :
    ∃ f : Fin n → ℂ → ℂ,
      (∀ j : Fin n, ∀ l ∈ L.lattice, ∀ z : ℂ, f j (z + l) = f j z) ∧
      (∀ i j : Fin n, f j (p i) = if i = j then 1 else 0) := by
  classical
  have hsep : ∀ j i : Fin n, ∃ c : ℂ,
      i ≠ j → L.weierstrassP (p j - c) ≠ L.weierstrassP (p i - c) := by
    intro j i
    by_cases hij : i = j
    · exact ⟨0, fun hne => absurd hij hne⟩
    · obtain ⟨c, hcne⟩ := exists_weierstrassP_translate_ne (hp j i fun hcc => hij hcc.symm)
      exact ⟨c, fun _ => hcne⟩
  choose c hc using hsep
  exact ⟨latticeLagrange L p c,
    fun j l hl z => latticeLagrange_add_lattice p c j hl z,
    fun i j => latticeLagrange_apply p c (fun j i hij => hc j i hij) i j⟩

/-! ### Distinctness of a nontorsion translation orbit -/

/-- The first `n` points of the orbit of a nontorsion translation are pairwise distinct modulo the
lattice. -/
theorem orbit_sub_notMem_lattice {a : ℂ}
    (ha : ∀ k : ℤ, k ≠ 0 → (k : ℂ) * a ∉ L.lattice) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ((i : ℕ) : ℂ) * a - ((j : ℕ) : ℂ) * a ∉ L.lattice := by
  have hk : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ≠ 0 := by
    intro hcon
    refine hij (Fin.ext ?_)
    omega
  have hcast : ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ) * a
      = ((i : ℕ) : ℂ) * a - ((j : ℕ) : ℂ) * a := by
    push_cast
    ring
  have := ha _ hk
  rwa [hcast] at this

/-- **Interpolation along a nontorsion orbit.**  For a nontorsion step `a` the first `n` orbit points
carry a lattice-periodic family with `f j (i • a) = δ_{ij}`. -/
theorem exists_latticePeriodic_interpolation_orbit {a : ℂ}
    (ha : ∀ k : ℤ, k ≠ 0 → (k : ℂ) * a ∉ L.lattice) (n : ℕ) :
    ∃ f : Fin n → ℂ → ℂ,
      (∀ j : Fin n, ∀ l ∈ L.lattice, ∀ z : ℂ, f j (z + l) = f j z) ∧
      (∀ i j : Fin n, f j (((i : ℕ) : ℂ) * a) = if i = j then 1 else 0) :=
  exists_latticePeriodic_interpolation (fun i => ((i : ℕ) : ℂ) * a)
    fun _ _ hij => orbit_sub_notMem_lattice ha hij

/-- **The orbit observation matrix of an interpolating family is the identity at the base point.**
This is the invertible observation packet that a finite-shadow capacity realization needs. -/
theorem orbitMatrix_eq_one {n : ℕ} {f : Fin n → ℂ → ℂ} {a : ℂ}
    (hf : ∀ i j : Fin n, f j (((i : ℕ) : ℂ) * a) = if i = j then 1 else 0) :
    (Matrix.of fun i j : Fin n => f j (0 + ((i : ℕ) : ℂ) * a)) = 1 := by
  ext i j
  rw [Matrix.of_apply, zero_add, hf i j, Matrix.one_apply]

end

end GaloisForLFunctions.HTGeometry
