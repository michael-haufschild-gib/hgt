import GaloisForLFunctions.RHTower.OddSectorGroundZeroInterpolation

/-!
# Exact finite spectral interpolation for OWU

At every positive aperture the actual canonical corrected odd ground generator
has simple nonzero zeros. Any finite selection with distinct squares supports
an exact positive interpolation problem in the same form domain. All minimizers
are classified by the already constructed ground space. No simplicity,
nonvanishing norming constant, pole constraint, or sign premise is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundQuadrature

private theorem shiftedForm_sum_left (a : SuzukiPositiveAperture) {ι : Type*}
    (s : Finset ι) (f : ι → CCMArchimedeanFormDomain a) (u : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (∑ i ∈ s, f i) u = ∑ i ∈ s, arithmeticShiftedForm a (f i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [arithmeticShiftedForm,arithmeticForm]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,arithmeticShiftedForm_add_left,ih]

private theorem finite_interpolation (a : SuzukiPositiveAperture) (n : ℕ)
    (z : Fin n → ℂ) (e : Fin n → CCMArchimedeanFormDomain a) (ρ : Fin n → ℝ)
    (heo : ∀ i, ccmArchimedeanFormReflection a (e i) = -e i)
    (hcard : ∀ i j, unitaryLaplace (timeRep a (e j)) (z i) = if i=j then 1 else 0)
    (hrep : ∀ i (u : CCMArchimedeanFormDomain a), ccmArchimedeanFormReflection a u = -u →
      arithmeticShiftedForm a (e i) u = (ρ i : ℂ)*unitaryLaplace (timeRep a u) (z i)) :
    ∀ b : Fin n → ℂ,
      ccmArchimedeanFormReflection a (∑ i, b i • e i) = -(∑ i, b i • e i) ∧
      (∀ i, unitaryLaplace (timeRep a (∑ j, b j • e j)) (z i) = b i) ∧
      (arithmeticShiftedForm a (∑ i, b i • e i) (∑ i, b i • e i)).re =
        ∑ i, ρ i * ‖b i‖^2 ∧
      ∀ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a u = -u →
        (∀ i, unitaryLaplace (timeRep a u) (z i) = b i) →
        (arithmeticShiftedForm a u u).re = (∑ i, ρ i * ‖b i‖^2) +
          (arithmeticShiftedForm a (u-∑ i, b i • e i) (u-∑ i, b i • e i)).re ∧
        ((arithmeticShiftedForm a u u).re = ∑ i, ρ i * ‖b i‖^2 ↔
          u-∑ i, b i • e i ∈ oddArithmeticGroundSpace a) := by
  classical
  intro b
  let v := ∑ i, b i • e i
  have hvo : ccmArchimedeanFormReflection a v = -v := by
    dsimp only [v]
    simp only [map_sum,map_smul,heo,smul_neg,Finset.sum_neg_distrib]
  have hval (i : Fin n) : unitaryLaplace (timeRep a v) (z i) = b i := by
    change (evalAt a (z i)) (∑ j, b j • e j) = b i
    simp only [map_sum,map_smul,evalAt_apply,smul_eq_mul,hcard]
    simp
  have hpair (u : CCMArchimedeanFormDomain a)
      (hu : ccmArchimedeanFormReflection a u = -u) :
      arithmeticShiftedForm a v u =
        ∑ i, conj (b i)*((ρ i : ℂ)*unitaryLaplace (timeRep a u) (z i)) := by
    rw [shiftedForm_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [arithmeticShiftedForm_smul_left,hrep i u hu]
  have henergy : (arithmeticShiftedForm a v v).re = ∑ i, ρ i * ‖b i‖^2 := by
    rw [hpair v hvo,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hval]
    have he : conj (b i)*((ρ i : ℂ)*b i) = (ρ i : ℂ)*(conj (b i)*b i) := by ring
    rw [he,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  refine ⟨hvo,hval,henergy,?_⟩
  intro u hu hb
  let r := u-v
  have hro : ccmArchimedeanFormReflection a r = -r := by
    dsimp only [r]
    rw [map_sub,hu,hvo,neg_sub_neg,neg_sub]
  have hrval (i : Fin n) : unitaryLaplace (timeRep a r) (z i) = 0 := by
    change (evalAt a (z i)) (u-v) = 0
    rw [map_sub,evalAt_apply,evalAt_apply,hb,hval,sub_self]
  have hvr : arithmeticShiftedForm a v r = 0 := by
    rw [hpair r hro]
    simp only [hrval,mul_zero,Finset.sum_const_zero]
  have hrv : arithmeticShiftedForm a r v = 0 := by
    rw [arithmeticShiftedForm_conj,hvr,map_zero]
  have hsplit : (arithmeticShiftedForm a u u).re =
      (∑ i, ρ i * ‖b i‖^2) + (arithmeticShiftedForm a r r).re := by
    have huvr : u = v+r := by dsimp only [r]; abel
    calc
      (arithmeticShiftedForm a u u).re =
          (arithmeticShiftedForm a v v).re + (arithmeticShiftedForm a r r).re := by
        conv_lhs => rw [huvr]
        rw [arithmeticShiftedForm_add_left,arithmeticShiftedForm_add_right,
          arithmeticShiftedForm_add_right,hvr,hrv,add_zero,zero_add,Complex.add_re]
      _ = _ := by rw [henergy]
  refine ⟨hsplit,?_⟩
  constructor
  · intro he
    apply (mem_oddArithmeticGroundSpace_iff a r).mpr
    exact ⟨hro,by linarith⟩
  · intro hr
    have hz := ((mem_oddArithmeticGroundSpace_iff a r).mp hr).2
    rw [hsplit,hz,add_zero]

/-- Unconditional OWU spectral interpolation: simple nonzero generator zeros,
positive cardinal coordinates, exact energies, and the full affine family of minimizers. -/
theorem exists_canonical_oddGround_exact_interpolation (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a, IsOddArithmeticGroundGenerator a G ∧
      (∀ z : ℂ, unitaryLaplace (timeRep a G) z = 0 → z.re = 0 ∨ z.im = 0) ∧
      (∀ z : ℂ, z ≠ 0 → unitaryLaplace (timeRep a G) z = 0 →
        deriv (unitaryLaplace (timeRep a G)) z ≠ 0) ∧
      ∃ (z : ℕ → ℂ) (e : ℕ → CCMArchimedeanFormDomain a) (ρ : ℕ → ℝ),
        Function.Injective (fun i => (z i)^2) ∧
        (∀ i, z i ≠ 0 ∧ unitaryLaplace (timeRep a G) (z i) = 0) ∧
        (∀ i, ccmArchimedeanFormReflection a (e i) = -e i) ∧
        (∀ i, 0 < ρ i) ∧
        (∀ i j, unitaryLaplace (timeRep a (e j)) (z i) = if i=j then 1 else 0) ∧
        (∀ i (u : CCMArchimedeanFormDomain a), ccmArchimedeanFormReflection a u = -u →
          arithmeticShiftedForm a (e i) u = (ρ i : ℂ)*unitaryLaplace (timeRep a u) (z i)) ∧
        ∀ (n : ℕ) (b : Fin n → ℂ),
          ccmArchimedeanFormReflection a (∑ i : Fin n, b i • e i) = -(∑ i : Fin n, b i • e i) ∧
          (∀ i : Fin n, unitaryLaplace (timeRep a (∑ j : Fin n, b j • e j)) (z i) = b i) ∧
          (arithmeticShiftedForm a (∑ i : Fin n, b i • e i) (∑ i : Fin n, b i • e i)).re =
            ∑ i : Fin n, ρ i * ‖b i‖^2 ∧
          ∀ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a u = -u →
            (∀ i : Fin n, unitaryLaplace (timeRep a u) (z i) = b i) →
            (arithmeticShiftedForm a u u).re = (∑ i : Fin n, ρ i * ‖b i‖^2) +
              (arithmeticShiftedForm a (u-∑ i : Fin n, b i • e i) (u-∑ i : Fin n, b i • e i)).re ∧
            ((arithmeticShiftedForm a u u).re = ∑ i : Fin n, ρ i * ‖b i‖^2 ↔
              u-∑ i : Fin n, b i • e i ∈ oddArithmeticGroundSpace a) := by
  classical
  obtain ⟨G,hG,hcross,_⟩ := exists_canonical_oddArithmeticGround_generator a
  have hc (z : ℂ) (hz : unitaryLaplace (timeRep a G) z = 0) : conj (z^2) = z^2 := by
    rcases hcross z hz with hr | hi
    · apply Complex.ext <;> simp [pow_two,Complex.mul_re,Complex.mul_im,hr]
    · apply Complex.ext <;> simp [pow_two,Complex.mul_re,Complex.mul_im,hi]
  obtain ⟨z,hinj,hz⟩ := exists_ccm_transform_squared_zero_sequence a G
  choose e ρ heo heval hρ hrep hzero using fun i =>
    exists_oddGround_zero_representative a hG (hz i).1 (hc (z i) (hz i).2) (hz i).2
  have hcard (i j : ℕ) :
      unitaryLaplace (timeRep a (e j)) (z i) = if i=j then 1 else 0 := by
    by_cases hij : i=j
    · subst j
      rw [heval,if_pos rfl]
    · rw [if_neg hij]
      exact hzero j (z i) (hz i).2 (fun he => hij (hinj he))
  refine ⟨G,hG,hcross,fun w hw0 hw => oddGroundGenerator_deriv_ne_zero a hG hw0 (hc w hw) hw,
    z,e,ρ,hinj,hz,heo,hρ,hcard,hrep,?_⟩
  intro n
  apply finite_interpolation a n (fun i : Fin n => z i) (fun i : Fin n => e i)
    (fun i : Fin n => ρ i) (fun i => heo i) ?_ (fun i => hrep i)
  intro i j
  simpa only [Fin.val_inj] using hcard i j

end RHTower.OddSector
