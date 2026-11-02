import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.ActualResidueGeometry
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.TwoPrimeResolventSeparation

/-!
# The actual boundary energy inequality

A near-boundary zero supplies an eighth-power height pole. Split the
remaining residues into a phase-coherent cluster, a bounded height region,
and a sixth-moment tail. Summing their negative contributions against the
uniform resolvent bound gives `A/H^8 ≤ B(s T^N + T⁻⁶)`.
-/

open Complex
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling

lemma exists_actual_far_resolvent_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ (ρ₀ ρ : zetaZeroConfig.carrier) (s T : ℝ),
      0 ≤ s → 1 ≤ T → |(ρ₀:ℂ).im| ≤ T → |(ρ:ℂ).im| ≤ T →
      r ≤ ‖boundaryOffset (ρ₀:ℂ).im s ρ‖ →
      ‖(1-boundaryClock (Real.log p) (Real.log q) (ρ₀:ℂ).im s ρ)⁻¹‖ ≤ C*T^N := by
  obtain ⟨c,hc,N,hsep⟩ := exists_two_prime_clockDefect_lower hp hq hpq hr
  refine ⟨4^N/c,N,div_pos (pow_pos (by norm_num) N) hc,?_⟩
  intro ρ₀ ρ s T hs hT hγ₀ hγ hfar
  let w := boundaryOffset (ρ₀:ℂ).im s ρ
  let f := clockDefect (Real.log p) (Real.log q) w
  have hbase : 0 < 2+|w.im| := by positivity
  have hlow := hsep w (boundaryOffset_re_nonpos _ hs ρ) hfar
  have hf : 0 < ‖f‖ := (div_pos hc (pow_pos hbase N)).trans_le hlow
  have hIm : |w.im| ≤ 2*T := by
    dsimp only [w]
    rw [boundaryOffset_im]
    exact (abs_sub _ _).trans (by linarith only [hγ,hγ₀])
  have hpw : (2+|w.im|)^N ≤ (4*T)^N :=
    pow_le_pow_left₀ hbase.le (by linarith only [hIm,hT]) N
  have hinv : 1/‖f‖ ≤ (2+|w.im|)^N/c := by
    apply (div_le_div_iff₀ hf hc).2
    have hh := (div_le_iff₀ (pow_pos hbase N)).mp hlow
    simpa only [one_mul,mul_one,mul_comm,f] using hh
  rw [← clockDefect_boundaryOffset,norm_inv,← one_div]
  calc
    _ ≤ (2+|w.im|)^N/c := hinv
    _ ≤ (4*T)^N/c := div_le_div_of_nonneg_right hpw hc.le
    _ = (4^N/c)*T^N := by rw [mul_pow]; ring

/-- A complex number admits a unit rotation to its nonnegative norm. -/
private lemma exists_aligning_unit (z : ℂ) : ∃ u : ℂ, ‖u‖=1 ∧ u*z=(‖z‖:ℂ) := by
  by_cases hz : z=0
  · exact ⟨1,by simp,by simp only [hz,norm_zero,Complex.ofReal_zero,mul_zero]⟩
  refine ⟨(‖z‖:ℂ)/z,?_,div_mul_cancel₀ _ hz⟩
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- A near-boundary atom must be paid for by polynomially bounded bulk
residues or the sixth-moment tail. All terms are actual zeta residues. -/
theorem exists_actual_boundary_energy_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hD : 0 < zetaZeroWidth)
    (hcone : ∃ M : ℝ, ∀ m n : ℕ,
      ‖coupling zetaKernel (primeElt hp^m) (primeElt hq^n)‖ ≤ M) :
    ∃ A B s₀ : ℝ, ∃ N : ℕ, 0 < A ∧ 0 < B ∧ 0 < s₀ ∧
      s₀ ≤ zetaZeroWidth/2 ∧ s₀ ≤ 1 ∧
      ∀ (ρ₀ : zetaZeroConfig.carrier) (s T : ℝ),
        0 < s → s ≤ s₀ → zetaZeroWidth-(zeroOffset ρ₀).re ≤ s →
        1+|(ρ₀:ℂ).im| ≤ T →
        A/(1+|(ρ₀:ℂ).im|)^8 ≤ B*(s*T^N+1/T^6) := by
  classical
  let a := Real.log p
  let b := Real.log q
  have ha : 0 < a := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < b := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨r,C,hr,hC,hnear⟩ := exists_actual_cluster_bound ha hb hD
  obtain ⟨F,N,hF,hfar⟩ := exists_actual_far_resolvent_bound hp hq hpq hr
  obtain ⟨K,hK,hglobal⟩ := exists_boundaryClock_inverse_bound ha hb
  obtain ⟨A,hA,hown⟩ := exists_actual_own_atom_lower ha hb hD
  obtain ⟨U,hU,huniform⟩ := exists_uniform_boundary_resolvent_bound hp hq hD hcone
  let M := ∑' ρ : zetaZeroConfig.carrier, ‖mixedResidue a b ρ‖
  let S := ∑' ρ : zetaZeroConfig.carrier, (1+|(ρ:ℂ).im|)^6*‖mixedResidue a b ρ‖
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  let B := 1+U+(C+F)*M+K*S
  have hB : 0 < B := by dsimp only [B]; positivity
  let s₀ := min (zetaZeroWidth/2) 1
  have hs₀ : 0 < s₀ := by dsimp only [s₀]; positivity
  refine ⟨A,B,s₀,N,hA,hB,hs₀,min_le_left _ _,min_le_right _ _,?_⟩
  intro ρ₀ s T hs hss₀ hgap hHT
  have hsD : s ≤ zetaZeroWidth/2 := hss₀.trans (min_le_left _ _)
  have hs1 : s ≤ 1 := hss₀.trans (min_le_right _ _)
  have hT1 : 1 ≤ T := (le_add_of_nonneg_right (abs_nonneg _)).trans hHT
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hγ₀ : |(ρ₀:ℂ).im| ≤ T := by linarith only [hHT]
  have hTN : 0 ≤ T^N := pow_nonneg hTp.le N
  have hTN1 : 1 ≤ T^N := one_le_pow₀ hT1
  obtain ⟨u,hu,hphase⟩ := exists_aligning_unit (splineResidue a b (zeroOffset ρ₀))
  let f : zetaZeroConfig.carrier → ℂ := fun ρ =>
    mixedResidue a b ρ/(1-boundaryClock a b (ρ₀:ℂ).im s ρ)
  let tail : zetaZeroConfig.carrier → ℝ := fun ρ =>
    if T < |(ρ:ℂ).im| then ‖mixedResidue a b ρ‖ else 0
  let e : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (C+F*T^N)*‖mixedResidue a b ρ‖+(K/s)*tail ρ
  have htail0 (ρ) : 0 ≤ tail ρ := by dsimp only [tail]; positivity
  have hetail : Summable tail :=
    (summable_norm_mixedResidue ha.le hb.le).of_nonneg_of_le htail0 (fun ρ => by
      dsimp only [tail]; split_ifs <;> simp only [le_refl,norm_nonneg])
  have he : Summable e :=
    ((summable_norm_mixedResidue ha.le hb.le).mul_left (C+F*T^N)).add (hetail.mul_left (K/s))
  have he0 (ρ) : 0 ≤ e ρ := by
    have ht := htail0 ρ
    dsimp only [e]
    positivity
  have heC (ρ) : C*‖mixedResidue a b ρ‖ ≤ e ρ := by
    have hh := mul_nonneg (mul_nonneg hF.le hTN) (norm_nonneg (mixedResidue a b ρ))
    have ht := mul_nonneg (div_nonneg hK.le hs.le) (htail0 ρ)
    dsimp only [e]
    nlinarith only [hh,ht]
  have heF (ρ) : F*T^N*‖mixedResidue a b ρ‖ ≤ e ρ := by
    have hh := mul_nonneg hC.le (norm_nonneg (mixedResidue a b ρ))
    have ht := mul_nonneg (div_nonneg hK.le hs.le) (htail0 ρ)
    dsimp only [e]
    nlinarith only [hh,ht]
  have hneg (ρ) : -(e ρ) ≤ (u*f ρ).re := by
    by_cases hn : ‖boundaryOffset (ρ₀:ℂ).im s ρ‖ ≤ r
    · exact (neg_le_neg (heC ρ)).trans (hnear ρ₀ ρ u s hs hsD hgap hu hphase hn)
    have hre := Complex.re_le_norm (-(u*f ρ))
    rw [Complex.neg_re,norm_neg] at hre
    have hnorm : ‖u*f ρ‖=‖mixedResidue a b ρ‖*
        ‖(1-boundaryClock a b (ρ₀:ℂ).im s ρ)⁻¹‖ := by
      simp only [f,div_eq_mul_inv,norm_mul,hu,one_mul]
    by_cases ht : |(ρ:ℂ).im| ≤ T
    · have hh := mul_le_mul_of_nonneg_left (hfar ρ₀ ρ s T hs.le hT1 hγ₀ ht (le_of_not_ge hn))
        (norm_nonneg (mixedResidue a b ρ))
      rw [← hnorm] at hh
      have he' := heF ρ
      nlinarith only [hre,hh,he']
    · have hh := mul_le_mul_of_nonneg_left (hglobal (ρ₀:ℂ).im s hs hs1 ρ)
        (norm_nonneg (mixedResidue a b ρ))
      rw [← hnorm] at hh
      have htail : tail ρ=‖mixedResidue a b ρ‖ := if_pos (lt_of_not_ge ht)
      have he' : K/s*‖mixedResidue a b ρ‖ ≤ e ρ := by
        have hnon := mul_nonneg (add_nonneg hC.le (mul_nonneg hF.le hTN))
          (norm_nonneg (mixedResidue a b ρ))
        dsimp only [e]
        rw [htail]
        linarith only [hnon]
      nlinarith only [hre,hh,he']
  have hf : Summable f := summable_boundary_resolvent ha hb hs _
  have haligned := aligned_atom_le_sum_norm_add_error hf he ρ₀ u hu (he0 ρ₀) (fun ρ _ => hneg ρ)
  have hown' := hown ρ₀ u s hs hsD hgap hphase
  have hnormsum : ‖∑' ρ, f ρ‖ ≤ U := huniform _ s hs
  have hesum : (∑' ρ, e ρ) ≤ (C+F*T^N)*M+(K/s)*S/(1+T)^6 := by
    rw [show (∑' ρ, e ρ)=(C+F*T^N)*M+(K/s)*(∑' ρ,tail ρ) by
      exact (((summable_norm_mixedResidue ha.le hb.le).hasSum.mul_left (C+F*T^N)).add
        (hetail.hasSum.mul_left (K/s))).tsum_eq]
    have ht := mul_le_mul_of_nonneg_left (mixedResidue_tail_le ha.le hb.le hTp.le)
      (div_nonneg hK.le hs.le)
    have ht' : (K/s)*(∑' ρ,tail ρ) ≤ (K/s)*S/(1+T)^6 := by
      calc
        _ ≤ (K/s)*(S/(1+T)^6) := ht
        _ = _ := by ring
    exact add_le_add le_rfl ht'
  have hraw : A/((1+|(ρ₀:ℂ).im|)^8*s) ≤ U+(C+F*T^N)*M+(K/s)*S/(1+T)^6 := by
    linarith only [hown',haligned,hnormsum,hesum]
  have hmul := mul_le_mul_of_nonneg_left hraw hs.le
  have hHpos : 0 < 1+|(ρ₀:ℂ).im| := by positivity
  have hTpos : 0 < 1+T := by positivity
  have hcancel : s*(A/((1+|(ρ₀:ℂ).im|)^8*s))=A/(1+|(ρ₀:ℂ).im|)^8 := by
    field_simp [hs.ne',hHpos.ne']
  have hcancel' : s*(U+(C+F*T^N)*M+(K/s)*S/(1+T)^6)=
      s*(U+(C+F*T^N)*M)+K*S/(1+T)^6 := by field_simp [hs.ne',hTpos.ne']
  rw [hcancel,hcancel'] at hmul
  have hbulk : U+(C+F*T^N)*M ≤ B*T^N := by
    have hh := mul_nonneg (add_nonneg hU (mul_nonneg hC.le hM)) (sub_nonneg.mpr hTN1)
    have hother := mul_nonneg (add_nonneg zero_le_one (mul_nonneg hK.le hS)) hTN
    dsimp only [B]
    nlinarith only [hh,hother]
  have htail : K*S/(1+T)^6 ≤ B/T^6 := by
    have hKB : K*S ≤ B := by
      have hh : 0 ≤ 1+U+(C+F)*M := by positivity
      dsimp only [B]
      linarith only [hh]
    exact (div_le_div_of_nonneg_left (mul_nonneg hK.le hS) (pow_pos hTp 6)
      (pow_le_pow_left₀ hTp.le (by linarith) 6)).trans
      (div_le_div_of_nonneg_right hKB (pow_nonneg hTp.le 6))
  calc
    _ ≤ s*(U+(C+F*T^N)*M)+K*S/(1+T)^6 := hmul
    _ ≤ s*(B*T^N)+B/T^6 := add_le_add (mul_le_mul_of_nonneg_left hbulk hs.le) htail
    _ = B*(s*T^N+1/T^6) := by ring

#print axioms exists_actual_far_resolvent_bound
#print axioms exists_actual_boundary_energy_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
