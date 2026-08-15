import GaloisForLFunctions.HTGeometry.SliceWeierstrassUnit
import GaloisForLFunctions.HTGeometry.DividedDifferencePolynomial

/-!
# Weierstrass' division theorem

Dividing a holomorphic function by the distinguished polynomial of a slice leaves a remainder which
is, in the distinguished variable, a polynomial of degree below the number of roots.  The quotient
is recovered from the boundary by a Cauchy integral, and the remainder is the Cauchy integral of the
divided difference of the distinguished polynomial — a polynomial in the evaluation point whose
coefficients are contour integrals of the parameters.
-/

open Complex Metric Set
open scoped Real Topology

namespace HTGeometry

open GaloisForLFunctions.HTGeometry (dividedDifferenceCoeff poly_sub_eq_mul_dividedDifference)

variable {n : ℕ}

/-! ### Coefficients of the distinguished polynomial -/

/-- The coefficients of the Weierstrass polynomial of a slice, in the distinguished variable. -/
noncomputable def sliceWeierstrassCoeff (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ)
    (j : ℕ) : ℂ :=
  (-1) ^ (Multiset.card (sliceRoots f t y) - j) *
    (sliceRoots f t y).esymm (Multiset.card (sliceRoots f t y) - j)

theorem sliceWeierstrass_eq_sum (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ) (z : ℂ) :
    sliceWeierstrass f t (Fin.cons z y)
      = ∑ j ∈ Finset.range (Multiset.card (sliceRoots f t y) + 1),
          sliceWeierstrassCoeff f t y j * z ^ j := by
  rw [sliceWeierstrass_cons, multisetLinearProd_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [sliceWeierstrassCoeff]

theorem continuous_sliceWeierstrass_slice (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ) :
    Continuous fun ζ : ℂ => sliceWeierstrass f t (Fin.cons ζ y) := by
  have hfun : (fun ζ : ℂ => sliceWeierstrass f t (Fin.cons ζ y))
      = multisetLinearProd (sliceRoots f t y) := by
    funext ζ
    rw [sliceWeierstrass_cons]
  rw [hfun]
  exact continuous_multisetLinearProd _

theorem continuous_dividedDifferenceCoeff (d : ℕ) (p : ℕ → ℂ) (k : ℕ) :
    Continuous fun ζ : ℂ => dividedDifferenceCoeff d p ζ k := by
  rw [show (fun ζ : ℂ => dividedDifferenceCoeff d p ζ k)
      = fun ζ : ℂ => ∑ j ∈ Finset.Ico (k + 1) (d + 1), p j * ζ ^ (j - 1 - k) from rfl]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow _)

/-! ### The quotient and the remainder -/

/-- The Cauchy integrand producing the Weierstrass quotient. -/
noncomputable def divIntegrand (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (v : Fin (n + 2) → ℂ) : ℂ :=
  (v 0 - (Fin.tail v) 0)⁻¹ *
    (g (Fin.cons (v 0) (Fin.tail (Fin.tail v)))
      / sliceWeierstrass f t (Fin.cons (v 0) (Fin.tail (Fin.tail v))))

@[simp]
theorem divIntegrand_cons (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (ζ : ℂ) (w : Fin (n + 1) → ℂ) :
    divIntegrand f g t (Fin.cons ζ w)
      = (ζ - w 0)⁻¹ *
        (g (Fin.cons ζ (Fin.tail w)) / sliceWeierstrass f t (Fin.cons ζ (Fin.tail w))) := by
  rw [divIntegrand, Fin.cons_zero, Fin.tail_cons]

/-- The Weierstrass quotient. -/
noncomputable def sliceDivQuotient (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ)
    (w : Fin (n + 1) → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ ζ in C(0, t), divIntegrand f g t (Fin.cons ζ w)

/-- The Weierstrass remainder. -/
noncomputable def sliceDivRemainder (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ)
    (w : Fin (n + 1) → ℂ) : ℂ :=
  g w - sliceDivQuotient f g t w * sliceWeierstrass f t w

theorem sliceDiv_eq (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (w : Fin (n + 1) → ℂ) :
    g w = sliceDivQuotient f g t w * sliceWeierstrass f t w + sliceDivRemainder f g t w := by
  rw [sliceDivRemainder]
  ring

/-- The `k`-th coefficient of the Weierstrass remainder. -/
noncomputable def sliceDivRemainderCoeff (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ)
    (y : Fin n → ℂ) (k : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ ζ in C(0, t), g (Fin.cons ζ y) *
      dividedDifferenceCoeff (Multiset.card (sliceRoots f t y)) (sliceWeierstrassCoeff f t y) ζ k
        / sliceWeierstrass f t (Fin.cons ζ y)

end HTGeometry

namespace HTGeometry

open Complex Metric Set
open scoped Real Topology
open GaloisForLFunctions.HTGeometry (dividedDifferenceCoeff poly_sub_eq_mul_dividedDifference)

variable {n : ℕ}

theorem circleIntegrable_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ∀ i ∈ s, CircleIntegrable (F i) c R) :
    CircleIntegrable (fun z => ∑ i ∈ s, F i z) c R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [CircleIntegrable]
  | insert a s ha ih =>
      have hint : ∀ i ∈ s, CircleIntegrable (F i) c R :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsplit : (fun z => ∑ i ∈ insert a s, F i z) = F a + (fun z => ∑ i ∈ s, F i z) := by
        funext z
        rw [Finset.sum_insert ha]
        rfl
      rw [hsplit]
      exact (hF a (Finset.mem_insert_self a s)).add (ih hint)

theorem circleIntegral_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ∀ i ∈ s, CircleIntegrable (F i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, F i z) = ∑ i ∈ s, ∮ z in C(c, R), F i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a s ha ih =>
      have hint : ∀ i ∈ s, CircleIntegrable (F i) c R :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsplit : (fun z => ∑ i ∈ insert a s, F i z) = fun z => F a z + ∑ i ∈ s, F i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsplit, Finset.sum_insert ha,
        circleIntegral.integral_add (hF a (Finset.mem_insert_self a s))
          (circleIntegrable_finsetSum s F c R hint), ih hint]

/-- **The Weierstrass remainder is a polynomial of degree below the number of roots.** -/
theorem sliceDivRemainder_eq_sum {f g : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y)
    {t₁ : ℝ} (ht₁ : t < t₁)
    (hg : DifferentiableOn ℂ (fun z => g (Fin.cons z y)) (ball (0 : ℂ) t₁))
    {z : ℂ} (hz : ‖z‖ < t) :
    sliceDivRemainder f g t (Fin.cons z y)
      = ∑ k ∈ Finset.range (Multiset.card (sliceRoots f t y)),
          sliceDivRemainderCoeff f g t y k * z ^ k := by
  classical
  set d := Multiset.card (sliceRoots f t y) with hd
  set Wc := sliceWeierstrassCoeff f t y with hWc
  set W : ℂ → ℂ := fun ζ => sliceWeierstrass f t (Fin.cons ζ y) with hW
  set G : ℂ → ℂ := fun ζ => g (Fin.cons ζ y) with hG
  have hclosed : closedBall (0 : ℂ) t ⊆ ball (0 : ℂ) t₁ := closedBall_subset_ball ht₁
  have hsphere : sphere (0 : ℂ) t ⊆ ball (0 : ℂ) t₁ :=
    fun ζ hζ => hclosed (sphere_subset_closedBall hζ)
  have hnorm : ∀ ζ ∈ sphere (0 : ℂ) t, ‖ζ‖ = t := by
    intro ζ hζ
    simpa using mem_sphere_iff_norm.1 hζ
  have hWne : ∀ ζ ∈ sphere (0 : ℂ) t, W ζ ≠ 0 := fun ζ hζ =>
    sliceWeierstrass_ne_zero_of_norm_eq ht hy (hnorm ζ hζ)
  have hzne : ∀ ζ ∈ sphere (0 : ℂ) t, ζ - z ≠ 0 := by
    intro ζ hζ hcon
    have : ‖ζ‖ = ‖z‖ := by rw [sub_eq_zero.mp hcon]
    rw [hnorm ζ hζ] at this
    exact absurd hz (by rw [← this]; exact lt_irrefl t)
  have hGcont : ContinuousOn G (sphere (0 : ℂ) t) :=
    (hg.continuousOn).mono hsphere
  have hWcont : Continuous W := continuous_sliceWeierstrass_slice f t y
  -- integrability of the two Cauchy pieces
  set A : ℂ → ℂ := fun ζ => (ζ - z)⁻¹ * G ζ with hA
  set B : ℂ → ℂ := fun ζ => W z * ((ζ - z)⁻¹ * (G ζ / W ζ)) with hB
  have hinvcont : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) (sphere (0 : ℂ) t) :=
    ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) hzne
  have hAint : CircleIntegrable A 0 t :=
    ContinuousOn.circleIntegrable ht.le (hinvcont.mul hGcont)
  have hBint : CircleIntegrable B 0 t := by
    refine ContinuousOn.circleIntegrable ht.le (continuousOn_const.mul (hinvcont.mul ?_))
    exact hGcont.div (hWcont.continuousOn) hWne
  -- Cauchy's integral formula for `g`
  have hzball : z ∈ ball (0 : ℂ) t := by
    rw [mem_ball_zero_iff]
    exact hz
  have hcauchy : (∮ ζ in C(0, t), A ζ) = (2 * (Real.pi : ℂ) * Complex.I) * G z := by
    have hsmul : (∮ ζ in C(0, t), (ζ - z)⁻¹ • G ζ) = (2 * (Real.pi : ℂ) * Complex.I) • G z := by
      refine Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty hzball ?_ ?_
      · exact (hg.mono hclosed).continuousOn
      · intro w hw
        exact hg.differentiableAt (isOpen_ball.mem_nhds (hclosed (ball_subset_closedBall hw.1)))
    simp only [smul_eq_mul] at hsmul
    exact hsmul
  -- the quotient times the Weierstrass polynomial
  have hqW : sliceDivQuotient f g t (Fin.cons z y) * sliceWeierstrass f t (Fin.cons z y)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ ζ in C(0, t), B ζ := by
    have hint : (∮ ζ in C(0, t), divIntegrand f g t (Fin.cons ζ (Fin.cons z y)))
        = ∮ ζ in C(0, t), (ζ - z)⁻¹ * (G ζ / W ζ) := by
      refine circleIntegral.integral_congr ht.le fun ζ _ => ?_
      rw [divIntegrand_cons, Fin.cons_zero, Fin.tail_cons]
    have hpull : (∮ ζ in C(0, t), B ζ)
        = W z * ∮ ζ in C(0, t), (ζ - z)⁻¹ * (G ζ / W ζ) := by
      rw [hB]
      have h := circleIntegral.integral_smul (W z) (fun ζ => (ζ - z)⁻¹ * (G ζ / W ζ)) 0 t
      simp only [smul_eq_mul] at h
      exact h
    rw [sliceDivQuotient, hint, hpull]
    rw [show sliceWeierstrass f t (Fin.cons z y) = W z from rfl]
    ring
  -- the remainder as a single contour integral
  have hAB : ∀ ζ ∈ sphere (0 : ℂ) t,
      A ζ - B ζ = ∑ k ∈ Finset.range d, z ^ k • (G ζ * dividedDifferenceCoeff d Wc ζ k / W ζ) := by
    intro ζ hζ
    have hdiff : W ζ - W z = (ζ - z) * ∑ k ∈ Finset.range d, dividedDifferenceCoeff d Wc ζ k * z ^ k := by
      rw [hW]
      simp only
      rw [sliceWeierstrass_eq_sum, sliceWeierstrass_eq_sum, ← hd, ← hWc]
      exact poly_sub_eq_mul_dividedDifference d Wc ζ z
    have hsum : ∑ k ∈ Finset.range d, z ^ k • (G ζ * dividedDifferenceCoeff d Wc ζ k / W ζ)
        = G ζ / W ζ * ∑ k ∈ Finset.range d, dividedDifferenceCoeff d Wc ζ k * z ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul]
      field_simp
    have hz0 := hzne ζ hζ
    have hW0 := hWne ζ hζ
    rw [hsum]
    show (ζ - z)⁻¹ * G ζ - W z * ((ζ - z)⁻¹ * (G ζ / W ζ))
      = G ζ / W ζ * ∑ k ∈ Finset.range d, dividedDifferenceCoeff d Wc ζ k * z ^ k
    have hS : ∑ k ∈ Finset.range d, dividedDifferenceCoeff d Wc ζ k * z ^ k
        = (W ζ - W z) / (ζ - z) := by
      rw [hdiff]
      field_simp
    rw [hS]
    field_simp
  have hsplit : (∮ ζ in C(0, t), A ζ) - (∮ ζ in C(0, t), B ζ)
      = ∮ ζ in C(0, t), ∑ k ∈ Finset.range d,
          z ^ k • (G ζ * dividedDifferenceCoeff d Wc ζ k / W ζ) := by
    rw [← circleIntegral.integral_sub hAint hBint]
    exact circleIntegral.integral_congr ht.le hAB
  have hFint : ∀ k ∈ Finset.range d,
      CircleIntegrable (fun ζ => z ^ k • (G ζ * dividedDifferenceCoeff d Wc ζ k / W ζ)) 0 t := by
    intro k _
    refine ContinuousOn.circleIntegrable ht.le ?_
    have hbase : ContinuousOn (fun ζ : ℂ => G ζ * dividedDifferenceCoeff d Wc ζ k / W ζ)
        (sphere (0 : ℂ) t) :=
      (hGcont.mul ((continuous_dividedDifferenceCoeff d Wc k).continuousOn)).div
        (hWcont.continuousOn) hWne
    have hres : ContinuousOn (fun ζ : ℂ => z ^ k * (G ζ * dividedDifferenceCoeff d Wc ζ k / W ζ))
        (sphere (0 : ℂ) t) := ContinuousOn.mul continuousOn_const hbase
    simpa only [smul_eq_mul] using hres
  rw [sliceDivRemainder, show g (Fin.cons z y) = G z from rfl, hqW]
  have hGz : G z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ ζ in C(0, t), A ζ := by
    rw [hcauchy]
    field_simp
  rw [hGz, ← mul_sub, hsplit, circleIntegral_finsetSum _ _ 0 t hFint]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [circleIntegral.integral_smul, sliceDivRemainderCoeff, smul_eq_mul, ← hd, ← hWc]
  ring

end HTGeometry

namespace HTGeometry

open Complex Metric Set
open scoped Real Topology

variable {n : ℕ}

/-- **Weierstrass' division theorem.**  A function holomorphic near the closed disc of a slice is
the distinguished polynomial of another slice times a holomorphic quotient, plus a polynomial in the
distinguished variable of degree below the number of roots. -/
theorem weierstrass_division {f g : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y)
    {t₁ : ℝ} (ht₁ : t < t₁)
    (hg : DifferentiableOn ℂ (fun z => g (Fin.cons z y)) (ball (0 : ℂ) t₁)) :
    ∀ z : ℂ, ‖z‖ < t →
      g (Fin.cons z y)
        = sliceDivQuotient f g t (Fin.cons z y) * sliceWeierstrass f t (Fin.cons z y)
          + ∑ k ∈ Finset.range (Multiset.card (sliceRoots f t y)),
              sliceDivRemainderCoeff f g t y k * z ^ k := by
  intro z hz
  rw [← sliceDivRemainder_eq_sum ht hy ht₁ hg hz]
  exact sliceDiv_eq f g t (Fin.cons z y)

end HTGeometry

namespace HTGeometry

open Complex Metric Set
open scoped Real Topology

variable {n : ℕ}

/-- **The Weierstrass quotient is holomorphic in all the variables.**  It is a contour integral
whose integrand is holomorphic on the open set where the contour variable avoids both the
evaluation point and the zeros of the distinguished polynomial. -/
theorem differentiableOn_sliceDivQuotient {f g : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U) (hgU : DifferentiableOn ℂ g U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    DifferentiableOn ℂ (sliceDivQuotient f g t)
      {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V ∧ ‖w 0‖ < t} := by
  classical
  set A : (Fin (n + 2) → ℂ) → (Fin (n + 1) → ℂ) :=
    fun v => Fin.cons (v 0) (Fin.tail (Fin.tail v)) with hA
  have hAdiff : Differentiable ℂ A := differentiable_consDropSecond
  set Wv : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} with hWv
  have hWvopen : IsOpen Wv := by
    have hcont : Continuous fun w : Fin (n + 1) → ℂ => Fin.tail w :=
      (tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).continuous
    exact hV.preimage hcont
  have hWdiff : DifferentiableOn ℂ (sliceWeierstrass f t) Wv :=
    differentiableOn_sliceWeierstrass hU hV hf ht hdisc hnez hadm hVconn hy₀
  set N : Set (Fin (n + 1) → ℂ) := Wv ∩ (sliceWeierstrass f t) ⁻¹' {(0 : ℂ)}ᶜ with hN
  have hNopen : IsOpen N :=
    hWdiff.continuousOn.isOpen_inter_preimage hWvopen isOpen_compl_singleton
  set D : (Fin (n + 2) → ℂ) → ℂ := fun v => v 0 - (Fin.tail v) 0 with hD
  have hDdiff : Differentiable ℂ D := by
    refine Differentiable.sub ?_ ?_
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ) 0).differentiable
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ)
        (0 : Fin (n + 1)).succ).differentiable
  set Ω : Set (Fin (n + 2) → ℂ) := A ⁻¹' (U ∩ N) ∩ D ⁻¹' {(0 : ℂ)}ᶜ with hΩ
  have hΩopen : IsOpen Ω :=
    ((hU.inter hNopen).preimage hAdiff.continuous).inter
      (isOpen_compl_singleton.preimage hDdiff.continuous)
  have hintdiff : DifferentiableOn ℂ (divIntegrand f g t) Ω := by
    intro v hv
    have hDv : D v ≠ 0 := hv.2
    have hAU : A v ∈ U := hv.1.1
    have hAN : A v ∈ N := hv.1.2
    have h1 : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ => (D v)⁻¹) v :=
      (hDdiff v).inv hDv
    have h2 : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ => g (A v)) v :=
      (hgU.differentiableAt (hU.mem_nhds hAU)).comp v (hAdiff v)
    have h3 : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ => sliceWeierstrass f t (A v)) v :=
      (hWdiff.differentiableAt (hWvopen.mem_nhds hAN.1)).comp v (hAdiff v)
    have h4 : sliceWeierstrass f t (A v) ≠ 0 := hAN.2
    have hmul : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ =>
        (D v)⁻¹ * (g (A v) * (sliceWeierstrass f t (A v))⁻¹)) v :=
      h1.mul (h2.mul (h3.inv h4))
    refine (hmul.congr_of_eventuallyEq ?_).differentiableWithinAt
    refine Filter.Eventually.of_forall fun u => ?_
    rw [divIntegrand, div_eq_mul_inv]
  set P : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V ∧ ‖w 0‖ < t} with hP
  have hPopen : IsOpen P := by
    have h1 : IsOpen {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} := hWvopen
    have h2 : IsOpen {w : Fin (n + 1) → ℂ | ‖w 0‖ < t} := by
      have hcont : Continuous fun w : Fin (n + 1) → ℂ => w 0 :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).continuous
      exact isOpen_lt (hcont.norm) continuous_const
    exact h1.inter h2
  have hmem : ∀ (θ : ℝ) (w : Fin (n + 1) → ℂ), w ∈ P →
      (Fin.cons (circleMap 0 t θ) w : Fin (n + 2) → ℂ) ∈ Ω := by
    intro θ w hw
    have hζt : ‖circleMap 0 t θ‖ = t := by simpa using abs_of_pos ht
    have hAv : A (Fin.cons (circleMap 0 t θ) w) = Fin.cons (circleMap 0 t θ) (Fin.tail w) := by
      simp [hA, Fin.tail_cons]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hAv]
      exact hdisc (Fin.tail w) hw.1 _ (le_of_eq hζt)
    · rw [hWv, Set.mem_setOf_eq, hAv, Fin.tail_cons]
      exact hw.1
    · rw [Set.mem_preimage, hAv]
      exact sliceWeierstrass_ne_zero_of_norm_eq ht (hadm (Fin.tail w) hw.1) hζt
    · have hval : D (Fin.cons (circleMap 0 t θ) w) = circleMap 0 t θ - w 0 := by
        simp [hD, Fin.tail_cons]
      rw [Set.mem_preimage, hval]
      intro hcon
      have heq0 : circleMap 0 t θ - w 0 = 0 := hcon
      have hce : circleMap 0 t θ = w 0 := sub_eq_zero.mp heq0
      rw [hce] at hζt
      exact absurd hw.2 (by rw [hζt]; exact lt_irrefl t)
  intro w hw
  have hcirc := differentiableAt_circleIntegral_slice_open hΩopen hPopen hintdiff ht
    (fun _ => (1 : ℂ)) (by fun_prop) hmem hw
  have hcongr : (fun w : Fin (n + 1) → ℂ =>
      ∮ ζ in C(0, t), (1 : ℂ) • divIntegrand f g t (Fin.cons ζ w))
      = fun w : Fin (n + 1) → ℂ => ∮ ζ in C(0, t), divIntegrand f g t (Fin.cons ζ w) := by
    funext w'
    simp
  rw [hcongr] at hcirc
  exact ((hcirc.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹)).differentiableWithinAt

end HTGeometry

namespace HTGeometry

open Complex Metric Set
open scoped Real Topology
open GaloisForLFunctions.HTGeometry (dividedDifferenceCoeff)

variable {n : ℕ}

/-- The joint integrand of the `k`-th remainder coefficient, at a fixed root count. -/
noncomputable def divRemIntegrand (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (d k : ℕ)
    (w : Fin (n + 1) → ℂ) : ℂ :=
  g w * (∑ j ∈ Finset.Ico (k + 1) (d + 1),
      ((-1 : ℂ) ^ (d - j) * (sliceRoots f t (Fin.tail w)).esymm (d - j)) * (w 0) ^ (j - 1 - k))
    / sliceWeierstrass f t w

theorem sliceDivRemainderCoeff_eq_integral (f g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ)
    (y : Fin n → ℂ) {d : ℕ} (hcard : Multiset.card (sliceRoots f t y) = d) (k : ℕ) :
    sliceDivRemainderCoeff f g t y k
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∮ ζ in C(0, t), divRemIntegrand f g t d k (Fin.cons ζ y) := by
  have hfun : (fun ζ : ℂ => g (Fin.cons ζ y) *
      dividedDifferenceCoeff (Multiset.card (sliceRoots f t y)) (sliceWeierstrassCoeff f t y) ζ k
        / sliceWeierstrass f t (Fin.cons ζ y))
      = fun ζ : ℂ => divRemIntegrand f g t d k (Fin.cons ζ y) := by
    funext ζ
    rw [divRemIntegrand, Fin.tail_cons, Fin.cons_zero, dividedDifferenceCoeff]
    congr 2
    rw [hcard]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sliceWeierstrassCoeff, hcard]
  rw [sliceDivRemainderCoeff, hfun]

end HTGeometry

namespace HTGeometry

open Complex Metric Set
open scoped Real Topology

variable {n : ℕ}

theorem differentiableOn_divRemIntegrand {f g : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U) (hgU : DifferentiableOn ℂ g U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) (d k : ℕ) :
    DifferentiableOn ℂ (divRemIntegrand f g t d k)
      (U ∩ ({w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} ∩
        (sliceWeierstrass f t) ⁻¹' {(0 : ℂ)}ᶜ)) := by
  classical
  set Wv : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} with hWv
  set S : Set (Fin (n + 1) → ℂ) := U ∩ (Wv ∩ (sliceWeierstrass f t) ⁻¹' {(0 : ℂ)}ᶜ) with hS
  have hSU : S ⊆ U := fun w hw => hw.1
  have hSWv : S ⊆ Wv := fun w hw => hw.2.1
  have htail : DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ => Fin.tail w) S :=
    ((tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).differentiable).differentiableOn
  have hmaps : Set.MapsTo (fun w : Fin (n + 1) → ℂ => Fin.tail w) S V := fun w hw => hw.2.1
  have hproj : DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ => w 0) S :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
      (0 : Fin (n + 1))).differentiable).differentiableOn
  have hterm : ∀ j ∈ Finset.Ico (k + 1) (d + 1), DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ =>
      ((-1 : ℂ) ^ (d - j) * (sliceRoots f t (Fin.tail w)).esymm (d - j)) * (w 0) ^ (j - 1 - k)) S := by
    intro j _
    have hesymm : DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ =>
        (sliceRoots f t (Fin.tail w)).esymm (d - j)) S :=
      (differentiableOn_esymm_sliceRoots hU hV hf ht hdisc hnez hadm (d - j)).comp htail hmaps
    exact (hesymm.const_mul ((-1 : ℂ) ^ (d - j))).mul (hproj.pow (j - 1 - k))
  have hsum := DifferentiableOn.sum (u := Finset.Ico (k + 1) (d + 1))
    (A := fun j (w : Fin (n + 1) → ℂ) =>
      ((-1 : ℂ) ^ (d - j) * (sliceRoots f t (Fin.tail w)).esymm (d - j)) * (w 0) ^ (j - 1 - k))
    hterm
  have hfun : (∑ j ∈ Finset.Ico (k + 1) (d + 1),
      fun w : Fin (n + 1) → ℂ =>
        ((-1 : ℂ) ^ (d - j) * (sliceRoots f t (Fin.tail w)).esymm (d - j)) * (w 0) ^ (j - 1 - k))
      = fun w : Fin (n + 1) → ℂ => ∑ j ∈ Finset.Ico (k + 1) (d + 1),
          ((-1 : ℂ) ^ (d - j) * (sliceRoots f t (Fin.tail w)).esymm (d - j)) *
            (w 0) ^ (j - 1 - k) := by
    funext w
    rw [Finset.sum_apply]
  rw [hfun] at hsum
  have hWS : DifferentiableOn ℂ (sliceWeierstrass f t) S :=
    (differentiableOn_sliceWeierstrass hU hV hf ht hdisc hnez hadm hVconn hy₀).mono hSWv
  have hWne : ∀ w ∈ S, sliceWeierstrass f t w ≠ 0 := fun w hw => hw.2.2
  exact ((hgU.mono hSU).mul hsum).div hWS hWne

/-- **The remainder coefficients are holomorphic in the parameters.** -/
theorem differentiableAt_sliceDivRemainderCoeff {f g : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U) (hgU : DifferentiableOn ℂ g U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) (k : ℕ) :
    DifferentiableAt ℂ (fun y : Fin n → ℂ => sliceDivRemainderCoeff f g t y k) y₀ := by
  classical
  set d : ℕ := Multiset.card (sliceRoots f t y₀) with hd
  have hcard : ∀ y ∈ V, Multiset.card (sliceRoots f t y) = d := fun y hy =>
    card_sliceRoots_const_of_isPreconnected hU hV hf ht hdisc hnez hadm hVconn hy hy₀
  set Wv : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} with hWv
  have hWvopen : IsOpen Wv := by
    have hcont : Continuous fun w : Fin (n + 1) → ℂ => Fin.tail w :=
      (tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).continuous
    exact hV.preimage hcont
  have hWdiff : DifferentiableOn ℂ (sliceWeierstrass f t) Wv :=
    differentiableOn_sliceWeierstrass hU hV hf ht hdisc hnez hadm hVconn hy₀
  set N : Set (Fin (n + 1) → ℂ) := Wv ∩ (sliceWeierstrass f t) ⁻¹' {(0 : ℂ)}ᶜ with hN
  have hNopen : IsOpen N :=
    hWdiff.continuousOn.isOpen_inter_preimage hWvopen isOpen_compl_singleton
  have hΩopen : IsOpen (U ∩ N) := hU.inter hNopen
  have hint : DifferentiableOn ℂ (divRemIntegrand f g t d k) (U ∩ N) :=
    differentiableOn_divRemIntegrand hU hV hf hgU ht hdisc hnez hadm hVconn hy₀ d k
  have hmemU : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V →
      (Fin.cons (circleMap 0 t θ) y : Fin (n + 1) → ℂ) ∈ U ∩ N := by
    intro θ y hy
    have hζt : ‖circleMap 0 t θ‖ = t := by simpa using abs_of_pos ht
    refine ⟨hdisc y hy _ (le_of_eq hζt), ?_, ?_⟩
    · rw [hWv, Set.mem_setOf_eq, Fin.tail_cons]
      exact hy
    · exact sliceWeierstrass_ne_zero_of_norm_eq ht (hadm y hy) hζt
  have hcirc := differentiableAt_circleIntegral_slice_open hΩopen hV hint ht
    (fun _ => (1 : ℂ)) (by fun_prop) hmemU hy₀
  have hcongr : (fun y : Fin n → ℂ =>
      ∮ ζ in C(0, t), (1 : ℂ) • divRemIntegrand f g t d k (Fin.cons ζ y))
      = fun y : Fin n → ℂ => ∮ ζ in C(0, t), divRemIntegrand f g t d k (Fin.cons ζ y) := by
    funext y
    simp
  rw [hcongr] at hcirc
  have hscaled := hcirc.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  refine hscaled.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hy₀] with y hy
  exact sliceDivRemainderCoeff_eq_integral f g t y (hcard y hy) k

end HTGeometry
