import GaloisForLFunctions.HTGeometry.PencilOperatorKernel

/-!
# The differential matroid of a periodic pencil over the operator ring

The kernel theorem says a `ℂ[δ]`-combination of pencil carriers is constant only if every
coefficient polynomial lies in the Stanley–Reisner ideal.  Read across a family of classes it says
that the carriers of `ℂ`-independent classes are independent over the whole operator ring `ℂ[δ]`,
not merely over `ℂ`: writing a combination `∑ᵢ 𝒟ᵢ · Pᵢ(T)F` with `𝒟ᵢ = ∑_r c_{i,r} δ^r` and
collecting powers of `δ` turns it into `∑_r δ^r (∑ᵢ c_{i,r} Pᵢ)(T)F`.

* `dirDeriv_iterate_const_mul`, `dirDeriv_iterate_sum` — linearity of the iterated derivation;
* `seedCarrierPoly_sum_smul` — linearity of the carrier assignment;
* `operatorFamily_eq` — the exchange of the two sums;
* `operatorFamily_kernel` — the kernel statement for a family;
* `operatorFamily_coeff_eq_zero` — `ℂ[δ]`-independence of the carriers of independent classes.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ} {α : Type*} [DecidableEq α] {facets : Finset (Finset α)}

/-! ### Linearity of the iterated derivation -/

theorem dirDeriv_iterate_const_mul (w : Fin d → ℂ) {f : (Fin d → ℂ) → ℂ}
    (hf : ∀ j : ℕ, Differentiable ℂ ((dirDeriv w)^[j] f)) (c : ℂ) (r : ℕ) :
    (dirDeriv w)^[r] (fun z => c * f z) = fun z => c * (dirDeriv w)^[r] f z := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, dirDeriv_const_mul (hf r) c w,
      ← Function.iterate_succ_apply' (dirDeriv w) r]

theorem dirDeriv_iterate_sum {ι : Type*} (s : Finset ι) (w : Fin d → ℂ)
    {f : ι → (Fin d → ℂ) → ℂ}
    (hf : ∀ i ∈ s, ∀ j : ℕ, Differentiable ℂ ((dirDeriv w)^[j] (f i))) (r : ℕ) :
    (dirDeriv w)^[r] (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, (dirDeriv w)^[r] (f i) z := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, dirDeriv_sum s (fun i hi => hf i hi r) w]
    funext z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.iterate_succ_apply']

/-! ### Linearity of the carrier assignment -/

omit [DecidableEq α] in
theorem seedCarrierPoly_sum_smul {E : Type*} [AddCommMonoid E] (ω : α → E) (F : E → ℂ)
    {m : ℕ} (c : Fin m → ℂ) (Q : Fin m → MvPolynomial α ℂ) :
    seedCarrierPoly ω F (∑ i : Fin m, c i • Q i)
      = fun z => ∑ i : Fin m, c i * seedCarrierPoly ω F (Q i) z := by
  have h : seedCarrierPolyₗ ω F (∑ i : Fin m, c i • Q i)
      = ∑ i : Fin m, c i • seedCarrierPolyₗ ω F (Q i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  funext z
  have hz := congrFun h z
  simp only [seedCarrierPolyₗ_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hz
  exact hz

/-! ### The operator combination of a family -/

omit [DecidableEq α] in
/-- **Collecting powers of the derivation.**  A `ℂ[δ]`-combination of the carriers of a family of
polynomials is the `δ`-graded carrier of the corresponding coefficient combinations. -/
theorem operatorFamily_eq (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z) (w : Fin d → ℂ)
    {m n : ℕ} (c : Fin m → Fin n → ℂ) (Q : Fin m → MvPolynomial α ℂ) :
    (∑ i : Fin m, ∑ r : Fin n,
        c i r • (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (Q i)))
      = ∑ r : Fin n,
        (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (∑ i : Fin m, c i r • Q i)) := by
  have hcar : ∀ i : Fin m, ∀ j : ℕ,
      Differentiable ℂ ((dirDeriv w)^[j] (seedCarrierPoly S.ω S.seed (Q i))) :=
    fun i j => differentiable_dirDeriv_iterate_seedCarrierPoly S Lin hLin (Q i) w j
  have key : ∀ r : Fin n,
      (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (∑ i : Fin m, c i r • Q i))
        = fun z => ∑ i : Fin m,
            c i r * (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (Q i)) z := by
    intro r
    have hscaled : ∀ i : Fin m, ∀ j : ℕ, Differentiable ℂ
        ((dirDeriv w)^[j] (fun z => c i r * seedCarrierPoly S.ω S.seed (Q i) z)) := by
      intro i j
      rw [dirDeriv_iterate_const_mul w (hcar i) (c i r) j]
      exact (hcar i j).const_mul _
    rw [seedCarrierPoly_sum_smul,
      dirDeriv_iterate_sum Finset.univ w (fun i _ => hscaled i) (r : ℕ)]
    funext z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dirDeriv_iterate_const_mul w (hcar i) (c i r) (r : ℕ)]
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact (congrFun (key r) z).symm

/-- **The kernel theorem for a family.**  If a `ℂ[δ]`-combination of the carriers of `Q₁,…,Q_m` is
constant, then for every power of the derivation the corresponding coefficient combination lies in
the Stanley–Reisner ideal. -/
theorem operatorFamily_kernel (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z)
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lin A w ≠ 0) {m n : ℕ} (c : Fin m → Fin n → ℂ)
    (Q : Fin m → MvPolynomial α ℂ)
    (hconst : ∀ z z' : Fin d → ℂ,
      (∑ i : Fin m, ∑ r : Fin n,
        c i r • (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (Q i))) z
      = (∑ i : Fin m, ∑ r : Fin n,
        c i r • (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (Q i))) z')
    (r : Fin n) : (∑ i : Fin m, c i r • Q i) ∈ stanleyReisnerIdeal ℂ facets := by
  refine operatorKernel S Lin hLin hanti w hw (fun r => ∑ i : Fin m, c i r • Q i) ?_ r
  intro z z'
  have hEq := operatorFamily_eq S Lin hLin w c Q
  rw [← hEq]
  exact hconst z z'

/-- **The carriers of independent classes are independent over the operator ring.**  If the
Stanley–Reisner classes of `Q₁,…,Q_m` are `ℂ`-linearly independent, then no nonzero
`ℂ[δ]`-combination of their carriers is constant. -/
theorem operatorFamily_coeff_eq_zero (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z)
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lin A w ≠ 0) {m n : ℕ} (Q : Fin m → MvPolynomial α ℂ)
    (hindep : LinearIndependent ℂ fun i : Fin m =>
      (Ideal.Quotient.mk (stanleyReisnerIdeal ℂ facets) (Q i) : stanleyReisnerRing ℂ facets))
    (c : Fin m → Fin n → ℂ)
    (hconst : ∀ z z' : Fin d → ℂ,
      (∑ i : Fin m, ∑ r : Fin n,
        c i r • (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (Q i))) z
      = (∑ i : Fin m, ∑ r : Fin n,
        c i r • (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (Q i))) z')
    (i : Fin m) (r : Fin n) : c i r = 0 := by
  have hmem := operatorFamily_kernel S Lin hLin hanti w hw c Q hconst r
  have hmk : (Ideal.Quotient.mkₐ ℂ (stanleyReisnerIdeal ℂ facets))
      (∑ i : Fin m, c i r • Q i) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sum] at hmk
  simp only [map_smul, Ideal.Quotient.mkₐ_eq_mk] at hmk
  exact Fintype.linearIndependent_iff.mp hindep (fun i => c i r) hmk i

end

end GaloisForLFunctions.HTGeometry
