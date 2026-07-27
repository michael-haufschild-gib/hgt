import GaloisForLFunctions.RHTower.DeningerCompleteCarrierSpectrumBounded

/-!
# A pre-Hilbert polarized package whose spectrum is unbounded on the critical line

`DeningerCompleteCarrierSpectrumBounded` shows that on a **complete** carrier the polarized
weight-one generator is bounded, so its eigenvalues cannot be `1/2 + i·gamma` over an unbounded set.
The arithmetic realisation therefore has to live on an incomplete pre-Hilbert carrier — which is what
the corpus's "nuclear cohomology before Hilbert completion" prescription asks for.

This file shows that requirement is satisfiable.  The carrier is the **algebraic** direct sum

`E = ⨁_(n : ℕ) ℂ²`,

realised as finitely supported functions on `ℕ × Fin 2` with the obvious inner product; it is the
dense algebraic subspace of the `ℓ²` sum, and it is not complete.  Blockwise it carries the
two-dimensional witness of `DeningerWeightOnePolarizationWitness` at parameter `t = n`, so the
generator is diagonal with eigenvalues

`1/2 ± i n`,   `n : ℕ`,

unbounded and all on the critical line.  Every polarization axiom holds.

The carrier's incompleteness is then not assumed but *derived*: `not_completeSpace_of_unbounded_spectrum`
applied to this package proves it directly.
-/

noncomputable section

open scoped ComplexConjugate
open GaloisForLFunctions.RHTower

namespace RHTower

namespace PreHilbertWitness

/-- The algebraic direct sum `⨁_n ℂ²`, as finitely supported functions on `ℕ × Fin 2`. -/
abbrev Carrier : Type := (ℕ × Fin 2) →₀ ℂ

/-- The inner product, summed over the support of the second argument. -/
def innerF (x y : Carrier) : ℂ :=
  y.sum fun p yp => conj (x p) * yp

theorem innerF_eq_sum_of_subset {x y : Carrier} {s : Finset (ℕ × Fin 2)}
    (hy : y.support ⊆ s) :
    innerF x y = ∑ p ∈ s, conj (x p) * y p := by
  refine Finsupp.sum_of_support_subset _ hy _ ?_
  intro i _
  simp

theorem innerF_conj_symm (x y : Carrier) : conj (innerF y x) = innerF x y := by
  classical
  rw [innerF_eq_sum_of_subset (x := y) (y := x) (s := x.support ∪ y.support)
      Finset.subset_union_left,
    innerF_eq_sum_of_subset (x := x) (y := y) (s := x.support ∪ y.support)
      Finset.subset_union_right,
    map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

theorem innerF_add_left (x y z : Carrier) : innerF (x + y) z = innerF x z + innerF y z := by
  classical
  rw [innerF_eq_sum_of_subset (x := x + y) (y := z) (s := z.support) (Finset.Subset.refl _),
    innerF_eq_sum_of_subset (x := x) (y := z) (s := z.support) (Finset.Subset.refl _),
    innerF_eq_sum_of_subset (x := y) (y := z) (s := z.support) (Finset.Subset.refl _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.add_apply, map_add]
  ring

theorem innerF_smul_left (x y : Carrier) (r : ℂ) :
    innerF (r • x) y = conj r * innerF x y := by
  classical
  rw [innerF_eq_sum_of_subset (x := r • x) (y := y) (s := y.support) (Finset.Subset.refl _),
    innerF_eq_sum_of_subset (x := x) (y := y) (s := y.support) (Finset.Subset.refl _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, map_mul]
  ring

theorem innerF_self_eq_sum (x : Carrier) :
    innerF x x = ∑ p ∈ x.support, ((‖x p‖ : ℂ)) ^ 2 := by
  rw [innerF_eq_sum_of_subset (x := x) (y := x) (s := x.support) (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact RCLike.conj_mul (x p)

theorem innerF_self_re_nonneg (x : Carrier) : 0 ≤ (innerF x x).re := by
  rw [innerF_self_eq_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun p _ => ?_
  simp [← Complex.ofReal_pow]

theorem innerF_definite (x : Carrier) (h : innerF x x = 0) : x = 0 := by
  classical
  have hre : (∑ p ∈ x.support, ((‖x p‖ : ℂ)) ^ 2).re = 0 := by
    rw [← innerF_self_eq_sum, h]
    simp
  rw [Complex.re_sum] at hre
  have hsum : ∑ p ∈ x.support, ‖x p‖ ^ 2 = 0 := by simpa [← Complex.ofReal_pow] using hre
  have hzero : ∀ p ∈ x.support, ‖x p‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun p _ => by positivity).mp hsum
  ext p
  by_cases hp : p ∈ x.support
  · have h2 := hzero p hp
    have hnorm : ‖x p‖ = 0 := by nlinarith [norm_nonneg (x p)]
    simpa using norm_eq_zero.mp hnorm
  · simpa using Finsupp.notMem_support_iff.mp hp

/-- The inner-product core of the algebraic direct sum. -/
instance core : InnerProductSpace.Core ℂ Carrier where
  inner := innerF
  conj_inner_symm := innerF_conj_symm
  re_inner_nonneg := innerF_self_re_nonneg
  add_left := innerF_add_left
  smul_left := innerF_smul_left
  definite := innerF_definite

instance : NormedAddCommGroup Carrier := core.toNormedAddCommGroup

instance : InnerProductSpace ℂ Carrier := InnerProductSpace.ofCore _

end PreHilbertWitness

end RHTower

namespace RHTower

namespace PreHilbertWitness

open scoped ComplexConjugate

/-! ## The Hodge star and the generator -/

/-- Swap of the two coordinates inside each block. -/
def sw : (ℕ × Fin 2) ≃ (ℕ × Fin 2) :=
  (Equiv.refl ℕ).prodCongr (Equiv.addRight (1 : Fin 2))

@[simp] theorem sw_apply (p : ℕ × Fin 2) : sw p = (p.1, p.2 + 1) := rfl

theorem sw_involutive (p : ℕ × Fin 2) : sw (sw p) = p := by
  have h : ∀ i : Fin 2, i + 1 + 1 = i := by decide
  obtain ⟨n, i⟩ := p
  simp [sw_apply, h]

/-- The blockwise sign of the Hodge star. -/
def eps (p : ℕ × Fin 2) : ℂ := if p.2 = 0 then -1 else 1

theorem eps_ne_zero (p : ℕ × Fin 2) : eps p ≠ 0 := by
  rw [eps]
  split <;> norm_num

theorem conj_eps (p : ℕ × Fin 2) : conj (eps p) = eps p := by
  rw [eps]
  split <;> simp

theorem eps_mul_eps_sw (p : ℕ × Fin 2) : eps p * eps (sw p) = -1 := by
  have h0 : ((0 : Fin 2) + 1) = 1 := by decide
  have h1 : ((1 : Fin 2) + 1) = 0 := by decide
  obtain ⟨n, i⟩ := p
  fin_cases i <;> norm_num [eps, sw_apply, h0, h1]

/-- The Hodge star, defined pointwise. -/
def sigmaFun (x : Carrier) : Carrier :=
  Finsupp.onFinset (x.support.image sw) (fun q => eps q * conj (x (sw q)))
    (by
      intro q hq
      dsimp only at hq
      have hx : x (sw q) ≠ 0 := by
        intro h
        rw [h] at hq
        simp at hq
      exact Finset.mem_image.mpr ⟨sw q, Finsupp.mem_support_iff.mpr hx, sw_involutive q⟩)

@[simp] theorem sigmaFun_apply (x : Carrier) (q : ℕ × Fin 2) :
    sigmaFun x q = eps q * conj (x (sw q)) := Finsupp.onFinset_apply

/-- The Hodge star as a conjugate-linear map. -/
def sigmaMap : Carrier →ₗ⋆[ℂ] Carrier where
  toFun := sigmaFun
  map_add' x y := by
    ext q
    simp
    ring
  map_smul' c x := by
    ext q
    simp
    ring

@[simp] theorem sigmaMap_apply (x : Carrier) (q : ℕ × Fin 2) :
    sigmaMap x q = eps q * conj (x (sw q)) := rfl

theorem sigmaMap_sq (x : Carrier) : sigmaMap (sigmaMap x) = -x := by
  ext q
  rw [sigmaMap_apply, Finsupp.neg_apply, sigmaMap_apply, map_mul, conj_eps, sw_involutive,
    RingHomCompTriple.comp_apply, RingHom.id_apply, ← mul_assoc, eps_mul_eps_sw]
  ring

/-- The odd `K`-real structure of the pre-Hilbert witness. -/
def kreal : KRealStructure true Carrier where
  sigma := sigmaMap
  sq v := by
    rw [sigmaMap_sq]
    simp [kRealParityAction]

end PreHilbertWitness

end RHTower

namespace RHTower

namespace PreHilbertWitness

open scoped ComplexConjugate

/-! ## The generator, the cup trace, and the polarization -/

/-- Eigenvalue attached to a coordinate: `1/2 + i n` on the first slot of block `n`, `1/2 - i n` on
the second. -/
def lam (t : ℕ → ℝ) (p : ℕ × Fin 2) : ℂ :=
  if p.2 = 0 then 1 / 2 + (t p.1 : ℂ) * Complex.I else 1 / 2 - (t p.1 : ℂ) * Complex.I

theorem conj_lam_sw (t : ℕ → ℝ) (p : ℕ × Fin 2) : conj (lam t (sw p)) = lam t p := by
  have h0 : ((0 : Fin 2) + 1) = 1 := by decide
  have h1 : ((1 : Fin 2) + 1) = 0 := by decide
  obtain ⟨n, i⟩ := p
  fin_cases i <;> simp [lam, sw_apply, h0, h1, Complex.ext_iff]

theorem conj_lam_add (t : ℕ → ℝ) (p : ℕ × Fin 2) : conj (lam t p) + lam t p = 1 := by
  rw [lam]
  split <;> simp [Complex.ext_iff] <;> norm_num

/-- The diagonal generator. -/
def thetaFun (t : ℕ → ℝ) (x : Carrier) : Carrier :=
  Finsupp.onFinset x.support (fun q => lam t q * x q)
    (by
      intro q hq
      dsimp only at hq
      have hx : x q ≠ 0 := by
        intro h
        rw [h] at hq
        simp at hq
      exact Finsupp.mem_support_iff.mpr hx)

@[simp] theorem thetaFun_apply (t : ℕ → ℝ) (x : Carrier) (q : ℕ × Fin 2) :
    thetaFun t x q = lam t q * x q := Finsupp.onFinset_apply

theorem thetaFun_support_subset (t : ℕ → ℝ) (x : Carrier) :
    (thetaFun t x).support ⊆ x.support :=
  Finsupp.support_onFinset_subset

/-- The generator as a linear endomorphism. -/
def thetaMap (t : ℕ → ℝ) : Module.End ℂ Carrier where
  toFun := thetaFun t
  map_add' x y := by
    ext q
    simp
    ring
  map_smul' c x := by
    ext q
    simp
    ring

@[simp] theorem thetaMap_apply (t : ℕ → ℝ) (x : Carrier) (q : ℕ × Fin 2) :
    thetaMap t x q = lam t q * x q := rfl

theorem inner_eq_innerF (x y : Carrier) : @inner ℂ Carrier _ x y = innerF x y := rfl

theorem inner_theta_add (t : ℕ → ℝ) (u v : Carrier) :
    @inner ℂ Carrier _ (thetaMap t u) v + @inner ℂ Carrier _ u (thetaMap t v)
      = @inner ℂ Carrier _ u v := by
  classical
  rw [inner_eq_innerF, inner_eq_innerF, inner_eq_innerF,
    innerF_eq_sum_of_subset (x := thetaMap t u) (y := v) (s := v.support)
      (Finset.Subset.refl _),
    innerF_eq_sum_of_subset (x := u) (y := thetaMap t v) (s := v.support)
      (thetaFun_support_subset t v),
    innerF_eq_sum_of_subset (x := u) (y := v) (s := v.support) (Finset.Subset.refl _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thetaMap_apply, thetaMap_apply, map_mul]
  calc conj (lam t p) * conj (u p) * v p + conj (u p) * (lam t p * v p)
      = (conj (lam t p) + lam t p) * (conj (u p) * v p) := by ring
    _ = conj (u p) * v p := by rw [conj_lam_add, one_mul]

/-- The cup trace, defined from the Hodge star and the inner product. -/
def cupForm : LinearMap.BilinForm ℂ Carrier :=
  LinearMap.mk₂ ℂ (fun a b => -@inner ℂ Carrier _ (sigmaMap b) a)
    (fun a₁ a₂ b => by dsimp only; rw [inner_add_right]; ring)
    (fun c a b => by dsimp only; rw [inner_smul_right, smul_eq_mul]; ring)
    (fun a b₁ b₂ => by dsimp only; rw [map_add, inner_add_left]; ring)
    (fun c a b => by
      dsimp only
      rw [map_smulₛₗ, inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply,
        smul_eq_mul]
      ring)

@[simp] theorem cupForm_apply (a b : Carrier) :
    cupForm a b = -@inner ℂ Carrier _ (sigmaMap b) a := rfl

theorem sigmaMap_eq_zero_iff (b : Carrier) : sigmaMap b = 0 ↔ b = 0 := by
  constructor
  · intro h
    have := sigmaMap_sq b
    rw [h, map_zero] at this
    simpa using this.symm
  · intro h
    rw [h, map_zero]

theorem cupForm_nondegenerate : cupForm.Nondegenerate := by
  constructor
  · intro a ha
    have h := ha (-sigmaMap a)
    rw [cupForm_apply, map_neg, sigmaMap_sq] at h
    simp only [neg_neg] at h
    have : @inner ℂ Carrier _ a a = 0 := by
      have h2 : -@inner ℂ Carrier _ a a = 0 := h
      linear_combination -h2
    exact inner_self_eq_zero.mp this
  · intro b hb
    have h := hb (sigmaMap b)
    rw [cupForm_apply] at h
    have h2 : @inner ℂ Carrier _ (sigmaMap b) (sigmaMap b) = 0 := by linear_combination -h
    exact (sigmaMap_eq_zero_iff b).mp (inner_self_eq_zero.mp h2)

theorem star_theta_witness (t : ℕ → ℝ) (x : Carrier) :
    sigmaMap (thetaMap t x) = thetaMap t (sigmaMap x) := by
  ext q
  rw [sigmaMap_apply, thetaMap_apply, thetaMap_apply, sigmaMap_apply, map_mul, conj_lam_sw]
  ring

/-- **The pre-Hilbert witness.**  All polarization axioms hold, and the generator has the unbounded
eigenvalue family `1/2 ± i n`. -/
def polarization (t : ℕ → ℝ) : DeningerWeightOnePolarization Carrier where
  theta := thetaMap t
  cupTrace := cupForm
  cup_nondegenerate := cupForm_nondegenerate
  star := kreal
  theta_cup a b := by
    show -@inner ℂ Carrier _ (sigmaMap b) (thetaMap t a)
      + -@inner ℂ Carrier _ (sigmaMap (thetaMap t b)) a
      = -@inner ℂ Carrier _ (sigmaMap b) a
    rw [star_theta_witness t b]
    have := inner_theta_add t (sigmaMap b) a
    linear_combination -this
  star_theta x := star_theta_witness t x
  inner_eq_cup_star x y := by
    show @inner ℂ Carrier _ x y = -@inner ℂ Carrier _ (sigmaMap (sigmaMap x)) y
    rw [sigmaMap_sq, inner_neg_left]
    ring

theorem thetaMap_eigen (t : ℕ → ℝ) (n : ℕ) :
    thetaMap t (Finsupp.single ((n, 0) : ℕ × Fin 2) 1)
      = (1 / 2 + (t n : ℂ) * Complex.I) • Finsupp.single ((n, 0) : ℕ × Fin 2) 1 := by
  ext q
  rw [thetaMap_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hq : ((n, 0) : ℕ × Fin 2) = q
  · subst hq
    simp [lam]
  · simp [hq]

/-- **The polarization axioms constrain the spectrum to the critical line and nothing more.**  For
*every* real sequence `t` there is a polarized weight-one package whose generator has eigenvalues
`1/2 + i t n`.  So no density, growth or arithmetic property of the spectrum is forced by the
polarization; all of that has to come from the trace formula. -/
theorem exists_polarization_with_prescribed_spectrum (t : ℕ → ℝ) (n : ℕ) :
    (polarization t).theta (Finsupp.single ((n, 0) : ℕ × Fin 2) 1)
      = (1 / 2 + (t n : ℂ) * Complex.I) • Finsupp.single ((n, 0) : ℕ × Fin 2) 1 :=
  thetaMap_eigen t n

/-- **The carrier is not complete**, and this is derived rather than assumed: as soon as the
prescribed spectrum is unbounded, `not_completeSpace_of_unbounded_spectrum` applies to the package
built on it. -/
theorem not_completeSpace_carrier (t : ℕ → ℝ) (ht : ∀ C : ℝ, ∃ n, C < |t n|) :
    ¬ CompleteSpace Carrier := by
  refine DeningerWeightOnePolarization.not_completeSpace_of_unbounded_spectrum (polarization t) ?_
  intro C
  obtain ⟨n, hn⟩ := ht C
  refine ⟨1 / 2 + (t n : ℂ) * Complex.I, Finsupp.single ((n, 0) : ℕ × Fin 2) 1, ?_,
    thetaMap_eigen t n, ?_⟩
  · simp
  · have him : (1 / 2 + (t n : ℂ) * Complex.I).im = t n := by simp
    have h := Complex.abs_im_le_norm (1 / 2 + (t n : ℂ) * Complex.I)
    rw [him] at h
    linarith

end PreHilbertWitness

end RHTower
