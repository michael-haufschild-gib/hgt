import GaloisForLFunctions.HTGeometry.SpectralAffineGauge
import GaloisForLFunctions.HTGeometry.AnalyticJetRealization

/-!
# The spectral Mobius gauge: precomposition with a Mobius change of variable

Every Mobius map of the spectral variable is a composite of affine maps and one inversion, so the
affine and inversion gauges compose to it.  Independence of a family at the Mobius image points
therefore transports to independence of the precomposed family.

This is the domain-side counterpart of the corpus's codomain Mobius gauge.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Jets only depend on the germ, so families agreeing on an open set have the same jet vectors
there. -/
theorem fullJetVec_congr {m : ℕ} {g h : Fin m → ℂ → ℂ} {V : Set ℂ} (hVo : IsOpen V)
    (hgh : ∀ i, ∀ v ∈ V, g i v = h i v) {w : ℂ} (hw : w ∈ V) :
    fullJetVec g w = fullJetVec h w := by
  funext v
  rcases v with u | ⟨i, k⟩
  · rfl
  · have heq : g i =ᶠ[nhds w] h i := by
      filter_upwards [hVo.mem_nhds hw] with v hv using hgh i v hv
    show iteratedDeriv k (g i) w = iteratedDeriv k (h i) w
    exact iteratedDeriv_congr_of_eventuallyEq heq k

/-- The domain of the inversion into an open set is open. -/
theorem isOpen_invDomain {U : Set ℂ} (hU : IsOpen U) : IsOpen {u : ℂ | u ≠ 0 ∧ u⁻¹ ∈ U} := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  have h1 : {v : ℂ | v ≠ 0} ∈ nhds u := isOpen_compl_singleton.mem_nhds hu.1
  have h2 : (fun v : ℂ => v⁻¹) ⁻¹' U ∈ nhds u := (continuousAt_inv₀ hu.1) (hU.mem_nhds hu.2)
  filter_upwards [h1, h2] with v hv1 hv2 using ⟨hv1, hv2⟩

theorem contDiffAt_affine (a b z : ℂ) : ContDiffAt ℂ (⊤ : ℕ∞) (fun v : ℂ => a * v + b) z :=
  (contDiffAt_const.mul contDiffAt_id).add contDiffAt_const

/-- **The spectral Mobius gauge.**  If a family satisfies no differential relation at the Mobius
image points, neither does the family precomposed with that Mobius map. -/
theorem fullJet_independent_comp_mobius {m : ℕ} {U V : Set ℂ} (hUo : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hVden : ∀ v ∈ V, c * v + d ≠ 0)
    (hVU : ∀ v ∈ V, (a * v + b) / (c * v + d) ∈ U)
    (hind : ∀ Q : MvPolynomial (FullJetIndex m) ℂ,
      (∀ w ∈ V, MvPolynomial.eval (fullJetVec g ((a * w + b) / (c * w + d))) Q = 0) → Q = 0)
    (P : MvPolynomial (FullJetIndex m) ℂ)
    (hP : ∀ w ∈ V,
      MvPolynomial.eval (fullJetVec (fun i v => g i ((a * v + b) / (c * v + d))) w) P = 0) :
    P = 0 := by
  rcases eq_or_ne c 0 with hc | hc
  · -- an affine change of variable
    have hd : d ≠ 0 := by
      intro hcon
      apply hdet
      rw [hc, hcon]
      ring
    have hane : a / d ≠ 0 := by
      refine div_ne_zero ?_ hd
      intro hcon
      apply hdet
      rw [hc, hcon]
      ring
    have hform : ∀ v : ℂ, (a / d) * v + b / d = (a * v + b) / (c * v + d) := by
      intro v
      rw [hc, zero_mul, zero_add]
      field_simp
    have hfam : (fun i v => g i ((a / d) * v + b / d))
        = fun i v => g i ((a * v + b) / (c * v + d)) := by
      funext i v
      rw [hform v]
    refine fullJet_independent_comp_affine (U := U) (V := V) (W := V) hUo hg hVo hane
      (fun v hv => by rw [hform v]; exact hVU v hv) (chi := id) (fun w hw => hw) ?_ P ?_
    · intro Q hQ
      refine hind Q fun w hw => ?_
      have := hQ w hw
      rw [show (id w : ℂ) = w from rfl, hform w] at this
      exact this
    · intro w hw
      rw [show (id w : ℂ) = w from rfl, hfam]
      exact hP w hw
  · -- a genuine Mobius change of variable
    have hBne : (b * c - a * d) / c ^ (2 : ℕ) ≠ 0 := by
      refine div_ne_zero ?_ (pow_ne_zero 2 hc)
      intro hcon
      apply hdet
      linear_combination -hcon
    have hCne : ∀ v ∈ V, v + d / c ≠ 0 := by
      intro v hv hcon
      refine hVden v hv ?_
      have hcv : c * (v + d / c) = c * v + d := by
        rw [mul_add, mul_div_cancel₀ d hc]
      rw [← hcv, hcon, mul_zero]
    have hform : ∀ v ∈ V, (b * c - a * d) / c ^ (2 : ℕ) * (v + d / c)⁻¹ + a / c
        = (a * v + b) / (c * v + d) := by
      intro v hv
      have hvC : v + d / c ≠ 0 := hCne v hv
      have hden : c * v + d ≠ 0 := hVden v hv
      have hcv : c * (v + d / c) = c * v + d := by
        rw [mul_add, mul_div_cancel₀ d hc]
      rw [← hcv]
      field_simp
      ring
    set A : ℂ := a / c with hA
    set C : ℂ := d / c with hC
    set B : ℂ := (b * c - a * d) / c ^ (2 : ℕ) with hB
    -- the intermediate families
    set U₂ : Set ℂ := {t : ℂ | B * t + A ∈ U} with hU₂
    have hU₂o : IsOpen U₂ := by
      rw [hU₂]
      exact hUo.preimage (by fun_prop)
    set g₂ : Fin m → ℂ → ℂ := fun i t => g i (B * t + A) with hg₂def
    have hg₂ : ∀ i, ∀ t ∈ U₂, ContDiffAt ℂ (⊤ : ℕ∞) (g₂ i) t := by
      intro i t ht
      exact (hg i _ ht).comp t (contDiffAt_affine B A t)
    set U₃ : Set ℂ := {u : ℂ | u ≠ 0 ∧ u⁻¹ ∈ U₂} with hU₃
    have hU₃o : IsOpen U₃ := isOpen_invDomain hU₂o
    set g₃ : Fin m → ℂ → ℂ := fun i u => g₂ i u⁻¹ with hg₃def
    have hg₃ : ∀ i, ∀ u ∈ U₃, ContDiffAt ℂ (⊤ : ℕ∞) (g₃ i) u := by
      intro i u hu
      exact (hg₂ i _ hu.2).comp u (contDiffAt_inv ℂ hu.1)
    have hchiA : ∀ w ∈ V, (w + C)⁻¹ ∈ U₂ := by
      intro w hw
      rw [hU₂]
      show B * (w + C)⁻¹ + A ∈ U
      rw [hform w hw]
      exact hVU w hw
    have hchiB : ∀ w ∈ V, w + C ∈ U₃ := by
      intro w hw
      exact ⟨hCne w hw, hchiA w hw⟩
    -- step one: the outer affine map
    have hind₂ : ∀ Q : MvPolynomial (FullJetIndex m) ℂ,
        (∀ w ∈ V, MvPolynomial.eval (fullJetVec g₂ ((w + C)⁻¹)) Q = 0) → Q = 0 := by
      intro Q hQ
      refine fullJet_independent_comp_affine (U := U) (V := U₂) (W := V) hUo hg hU₂o hBne
        (fun t ht => ht) (chi := fun w => (w + C)⁻¹) hchiA ?_ Q ?_
      · intro R hR
        refine hind R fun w hw => ?_
        have hval := hR w hw
        rw [hform w hw] at hval
        exact hval
      · exact hQ
    -- step two: the inversion
    have hind₃ : ∀ Q : MvPolynomial (FullJetIndex m) ℂ,
        (∀ w ∈ V, MvPolynomial.eval (fullJetVec g₃ (w + C)) Q = 0) → Q = 0 := by
      intro Q hQ
      refine fullJet_independent_comp_inv (U := U₂) (V := U₃) (W := V) hU₂o hg₂ hU₃o
        (fun u hu => hu.1) (fun u hu => hu.2) (chi := fun w => w + C) hchiB ?_ Q ?_
      · exact hind₂
      · exact hQ
    -- step three: the inner translation
    have hind₄ : ∀ Q : MvPolynomial (FullJetIndex m) ℂ,
        (∀ w ∈ V, MvPolynomial.eval (fullJetVec (fun i v => g₃ i (1 * v + C)) w) Q = 0) →
          Q = 0 := by
      intro Q hQ
      refine fullJet_independent_comp_affine (U := U₃) (V := {v : ℂ | 1 * v + C ∈ U₃})
        (W := V) hU₃o hg₃ ?_ one_ne_zero (fun t ht => ht) (chi := id) ?_ ?_ Q ?_
      · exact hU₃o.preimage (by fun_prop)
      · intro w hw
        show 1 * w + C ∈ U₃
        rw [one_mul]
        exact hchiB w hw
      · intro R hR
        refine hind₃ R fun w hw => ?_
        have hval := hR w hw
        rw [show (id w : ℂ) = w from rfl, one_mul] at hval
        exact hval
      · intro w hw
        rw [show (id w : ℂ) = w from rfl]
        exact hQ w hw
    -- the composed family is the Mobius precomposition on `V`
    refine hind₄ P fun w hw => ?_
    have hfam : ∀ i, ∀ v ∈ V, (fun i v => g i ((a * v + b) / (c * v + d))) i v
        = (fun i v => g₃ i (1 * v + C)) i v := by
      intro i v hv
      show g i ((a * v + b) / (c * v + d)) = g₂ i (1 * v + C)⁻¹
      rw [hg₂def, one_mul]
      show g i ((a * v + b) / (c * v + d)) = g i (B * (v + C)⁻¹ + A)
      rw [hform v hv]
    rw [← fullJetVec_congr hVo hfam hw]
    exact hP w hw


/-- The domain of a Mobius map into an open set is open. -/
theorem isOpen_mobiusPreimage {V : Set ℂ} (hV : IsOpen V) (p q r s : ℂ) :
    IsOpen {z : ℂ | r * z + s ≠ 0 ∧ (p * z + q) / (r * z + s) ∈ V} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have h1 : {v : ℂ | r * v + s ≠ 0} ∈ nhds z := by
    have hopen : IsOpen {v : ℂ | r * v + s ≠ 0} := isOpen_compl_singleton.preimage (by fun_prop)
    exact hopen.mem_nhds hz.1
  have hcont : ContinuousAt (fun v : ℂ => (p * v + q) / (r * v + s)) z :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hz.1
  have h2 : (fun v : ℂ => (p * v + q) / (r * v + s)) ⁻¹' V ∈ nhds z := hcont (hV.mem_nhds hz.2)
  filter_upwards [h1, h2] with v hv1 hv2 using ⟨hv1, hv2⟩

/-- **Independence at Mobius sample points.**  For an analytic family on a connected domain,
independence on the domain gives independence at the image points of a Mobius map, because those
points fill an open subdomain: the inverse Mobius map exhibits it. -/
theorem fullJet_independent_at_mobius_points {m : ℕ} {U V : Set ℂ} (hUc : IsPreconnected U)
    {g : Fin m → ℂ → ℂ} (hga : ∀ i, AnalyticOnNhd ℂ (g i) U) (hVo : IsOpen V)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hVden : ∀ v ∈ V, c * v + d ≠ 0)
    (hVU : ∀ v ∈ V, (a * v + b) / (c * v + d) ∈ U) {w₀ : ℂ} (hw₀ : w₀ ∈ V)
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec g z) P = 0) → P = 0)
    (Q : MvPolynomial (FullJetIndex m) ℂ)
    (hQ : ∀ w ∈ V, MvPolynomial.eval (fullJetVec g ((a * w + b) / (c * w + d))) Q = 0) :
    Q = 0 := by
  set W : Set ℂ := {z : ℂ | -c * z + a ≠ 0 ∧ (d * z + -b) / (-c * z + a) ∈ V} with hWdef
  have hWo : IsOpen W := isOpen_mobiusPreimage hVo d (-b) (-c) a
  -- the inverse Mobius map returns the original point
  have hback : ∀ z ∈ W, (a * ((d * z + -b) / (-c * z + a)) + b)
      / (c * ((d * z + -b) / (-c * z + a)) + d) = z := by
    intro z hz
    have hz1 : -c * z + a ≠ 0 := hz.1
    have hXD : (d * z + -b) / (-c * z + a) * (-c * z + a) = d * z + -b :=
      div_mul_cancel₀ _ hz1
    have hnum : a * ((d * z + -b) / (-c * z + a)) + b
        = (a * d - b * c) * z / (-c * z + a) := by
      rw [eq_div_iff hz1, add_mul, mul_assoc, hXD]
      ring
    have hden : c * ((d * z + -b) / (-c * z + a)) + d
        = (a * d - b * c) / (-c * z + a) := by
      rw [eq_div_iff hz1, add_mul, mul_assoc, hXD]
      ring
    have hMD : (a * d - b * c) / (-c * z + a) ≠ 0 := div_ne_zero hdet hz1
    rw [hnum, hden, div_eq_iff hMD]
    ring
  have hWU : W ⊆ U := by
    intro z hz
    have hmem : (d * z + -b) / (-c * z + a) ∈ V := hz.2
    have := hVU _ hmem
    rwa [hback z hz] at this
  have hz₀ : (a * w₀ + b) / (c * w₀ + d) ∈ W := by
    have hden0 : c * w₀ + d ≠ 0 := hVden w₀ hw₀
    have hXD0 : (a * w₀ + b) / (c * w₀ + d) * (c * w₀ + d) = a * w₀ + b :=
      div_mul_cancel₀ _ hden0
    have h1 : -c * ((a * w₀ + b) / (c * w₀ + d)) + a = (a * d - b * c) / (c * w₀ + d) := by
      rw [eq_div_iff hden0, add_mul, mul_assoc, hXD0]
      ring
    have h1ne : -c * ((a * w₀ + b) / (c * w₀ + d)) + a ≠ 0 := by
      rw [h1]
      exact div_ne_zero hdet hden0
    refine ⟨h1ne, ?_⟩
    have h2 : (d * ((a * w₀ + b) / (c * w₀ + d)) + -b)
        = (a * d - b * c) * w₀ / (c * w₀ + d) := by
      rw [eq_div_iff hden0, add_mul, mul_assoc, hXD0]
      ring
    have hval : (a * d - b * c) * w₀ / (c * w₀ + d) / ((a * d - b * c) / (c * w₀ + d)) = w₀ := by
      rw [div_eq_iff (div_ne_zero hdet hden0)]
      ring
    rw [h2, h1, hval]
    exact hw₀
  refine fullJet_independent_mono hUc hga hWo hWU hz₀ hind Q ?_
  intro z hz
  have hval := hQ _ hz.2
  rwa [hback z hz] at hval

/-- **The Mobius domain gauge, in independence form.**  A family that is independent on a connected
analytic domain stays independent after precomposition with a Mobius change of variable. -/
theorem fullJet_independent_comp_mobius_of_independent {m : ℕ} {U V : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {g : Fin m → ℂ → ℂ} (hga : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hVo : IsOpen V) {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hVden : ∀ v ∈ V, c * v + d ≠ 0)
    (hVU : ∀ v ∈ V, (a * v + b) / (c * v + d) ∈ U) {w₀ : ℂ} (hw₀ : w₀ ∈ V)
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec g z) P = 0) → P = 0)
    (P : MvPolynomial (FullJetIndex m) ℂ)
    (hP : ∀ w ∈ V,
      MvPolynomial.eval (fullJetVec (fun i v => g i ((a * v + b) / (c * v + d))) w) P = 0) :
    P = 0 := by
  refine fullJet_independent_comp_mobius hUo
    (fun i => contDiffAt_of_analyticOnNhd (hga i)) hVo hdet hVden hVU ?_ P hP
  intro Q hQ
  exact fullJet_independent_at_mobius_points hUc hga hVo hdet hVden hVU hw₀ hind Q hQ


/-- **The Mobius domain gauge, corpus form.**  Precomposing an analytic family on a connected domain
with a Mobius change of variable preserves the absence of differential relations. -/
theorem not_familyDifferentiallyAlgebraicOn_comp_mobius {m : ℕ} {U V : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {g : Fin m → ℂ → ℂ} (hga : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hVo : IsOpen V) {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hVden : ∀ v ∈ V, c * v + d ≠ 0)
    (hVU : ∀ v ∈ V, (a * v + b) / (c * v + d) ∈ U) {w₀ : ℂ} (hw₀ : w₀ ∈ V)
    (hind : ¬ FamilyDifferentiallyAlgebraicOn g U) :
    ¬ FamilyDifferentiallyAlgebraicOn (fun i v => g i ((a * v + b) / (c * v + d))) V := by
  refine not_familyDifferentiallyAlgebraicOn_of_fullJet_independent fun P hP => ?_
  exact fullJet_independent_comp_mobius_of_independent hUo hUc hga hVo hdet hVden hVU hw₀
    (fun Q hQ => fullJet_independent_of_not_familyDifferentiallyAlgebraicOn hind Q hQ) P hP

end

end GaloisForLFunctions.HTGeometry
