import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitive
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockTopFrequency
import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology Set
namespace RHTower
noncomputable section

private theorem pn_cosine_re (w : ℂ) (t : ℝ) :
    (1 - Complex.cos ((t : ℂ) * w)).re =
      1 - Real.cos (t * w.re) * Real.cosh (t * w.im) := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im, -Complex.ofReal_mul,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re]

private theorem pn_normalized_atom (w : ℂ) {b : ℝ}
    (hw : |w.im| = b) (t : ℝ) :
    Real.exp (-b*t) * (1 - Complex.cos ((t : ℂ)*w)).re =
      Real.exp (-b*t) - ((1+Real.exp (-2*b*t))/2)*Real.cos (t*w.re) := by
  have hi : w.im = b ∨ w.im = -b := by
    rcases le_total 0 w.im with h | h
    · left
      simpa only [abs_of_nonneg h] using hw
    · right
      rw [abs_of_nonpos h] at hw
      linarith
  have hc : Real.cosh (t*w.im) = Real.cosh (t*b) := by
    rcases hi with h | h
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hp : Real.exp (-b*t)*Real.exp (t*b) = 1 := by
    rw [← Real.exp_add, show -b*t+t*b=0 by ring, Real.exp_zero]
  have hn : Real.exp (-b*t)*Real.exp (-(t*b)) = Real.exp (-2*b*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcosh : Real.exp (-b*t)*Real.cosh (t*b) = (1+Real.exp (-2*b*t))/2 := by
    rw [Real.cosh_eq]
    calc
      _ = (Real.exp (-b*t)*Real.exp (t*b) + Real.exp (-b*t)*Real.exp (-(t*b)))/2 := by ring
      _ = _ := by rw [hp, hn]
  rw [pn_cosine_re, hc]
  calc
    _ = Real.exp (-b*t) - (Real.exp (-b*t)*Real.cosh (t*b))*Real.cos (t*w.re) := by ring
    _ = _ := by rw [hcosh]

private theorem pn_finite_negative_limit {ι : Type*} [Fintype ι]
    (w : ι → ℂ) {b : ℝ} (hb : 0 < b) (hw : ∀ j, |(w j).im| = b) :
    ∃ t : ℕ → ℝ, (∀ n : ℕ, (n : ℝ)+1 ≤ t n) ∧
      Tendsto t atTop atTop ∧
      Tendsto (fun n => Real.exp (-b*t n) *
        ∑ j, (1-Complex.cos ((t n : ℂ)*w j)).re)
        atTop (𝓝 (-(Fintype.card ι : ℝ)/2)) := by
  classical
  have hrec (n : ℕ) : ∃ t : ℝ, (n : ℝ)+1 ≤ t ∧
      ∀ j, ‖GaloisForLFunctions.bohrChar (-(w j).re) t - 1‖ ≤
        1/((n : ℝ)+1) :=
    exists_simultaneous_phase_recurrence (fun j => -(w j).re)
      (by positivity) ((n : ℝ)+1)
  choose t ht hphase using hrec
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htop : Tendsto t atTop atTop := tendsto_atTop_mono ht hnat
  have heps : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hchar (j : ι) :
      Tendsto (fun n => GaloisForLFunctions.bohrChar (-(w j).re) (t n))
        atTop (𝓝 1) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => by simpa only [dist_eq_norm] using hphase n j) heps
  have hchar_eq (n : ℕ) (j : ι) :
      GaloisForLFunctions.bohrChar (-(w j).re) (t n) =
        Complex.exp ((t n * (w j).re : ℝ)*Complex.I) := by
    have ha : - (-(w j).re*t n) = t n*(w j).re := by ring
    rw [GaloisForLFunctions.bohrChar, ha]
  have hcos (j : ι) : Tendsto (fun n => Real.cos (t n*(w j).re)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, hchar_eq, Complex.exp_ofReal_mul_I_re, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : ℂ)).comp (hchar j)
  have hexp : Tendsto (fun n => Real.exp (-b*t n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (htop.const_mul_atTop_of_neg (by linarith))
  have hexp2 : Tendsto (fun n => Real.exp (-2*b*t n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (htop.const_mul_atTop_of_neg (by linarith))
  have hatom (j : ι) : Tendsto (fun n => Real.exp (-b*t n)*
      (1-Complex.cos ((t n : ℂ)*w j)).re) atTop (𝓝 (-(1 : ℝ)/2)) := by
    simp_rw [pn_normalized_atom (w j) (hw j)]
    have h := hexp.sub ((((tendsto_const_nhds (x := (1 : ℝ))).add hexp2).div_const 2).mul (hcos j))
    simpa only [add_zero, mul_one, zero_sub, neg_div] using h
  refine ⟨t, ht, htop, ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hatom j)
  have hc : (Fintype.card ι : ℝ)*(-(1 : ℝ)/2) = -(Fintype.card ι : ℝ)/2 := by ring
  simpa only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc] using hsum

private theorem pn_mass_summable :
    Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖^2) := by
  simpa only [norm_inv, one_div, inv_pow] using xiSpectralPoint_inv_sq_summable

private theorem pn_mass_eq :
    (∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖^2) = xiShiftAbsoluteMass 0 := by
  simp [xiShiftAbsoluteMass, xiZeroCopyReciprocalSquare, norm_pow]

private theorem pn_norm_complement_le (Q : Set XiZeroCopy) [DecidablePred (· ∈ Q)] {t β : ℝ}
    (hβ : ∀ q, q ∉ Q → |((xiSpectralPoint q)⁻¹).im| ≤ β)
    (ht : 0 ≤ t) :
    ‖∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom t q‖ ≤
      xiShiftAbsoluteMass 0*(t^2/2)*Real.exp (β*t) := by
  classical
  have hn : Summable (fun q : XiZeroCopy =>
      ‖if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom t q‖) := by
    apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _
      (summable_norm_liEvenCrossActualClockCosineAtom t)
    intro q
    by_cases hq : q ∈ Q <;> simp [hq]
  have hb (q : XiZeroCopy) :
      ‖if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom t q‖ ≤
        ‖(xiSpectralPoint q)⁻¹‖^2*(t^2/2*Real.exp (β*t)) := by
    by_cases hq : q ∈ Q
    · simp only [hq, if_pos, norm_zero]
      positivity
    · simp only [hq, if_false, liEvenCrossActualClockCosineAtom]
      have he : Real.exp (|t| * |((xiSpectralPoint q)⁻¹).im|) ≤ Real.exp (β*t) := by
        rw [abs_of_nonneg ht]
        apply Real.exp_le_exp.mpr
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hβ q hq) ht
      exact (liClock_norm_one_sub_cos_le_imaginary_exp t ((xiSpectralPoint q)⁻¹)).trans
        ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  calc
    _ ≤ ∑' q : XiZeroCopy, ‖if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom t q‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖^2*(t^2/2*Real.exp (β*t)) :=
      Summable.tsum_le_tsum hb hn (pn_mass_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right, pn_mass_eq]; ring

private theorem pn_quadratic_exp_gap {β b : ℝ} (hgap : β < b) (W : ℝ) :
    Tendsto (fun t : ℝ => W*(t^2/2)*Real.exp (-(b-β)*t)) atTop (𝓝 0) := by
  have hδ : 0 < b-β := sub_pos.mpr hgap
  have hbase : Tendsto (fun t : ℝ => ((b-β)*t)^2*Real.exp (-((b-β)*t)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (tendsto_id.const_mul_atTop hδ)
  have heq : (fun t : ℝ => (W/(2*(b-β)^2))*(((b-β)*t)^2*Real.exp (-((b-β)*t)))) =
      (fun t : ℝ => W*(t^2/2)*Real.exp (-(b-β)*t)) := by
    funext t
    rw [neg_mul]
    field_simp [hδ.ne']
  rw [← heq]
  simpa only [mul_zero] using hbase.const_mul (W/(2*(b-β)^2))

private theorem pn_complement_tendsto (Q : Set XiZeroCopy) [DecidablePred (· ∈ Q)] {β b : ℝ}
    (hβ : ∀ q, q ∉ Q → |((xiSpectralPoint q)⁻¹).im| ≤ β) (hgap : β < b) :
    Tendsto (fun t : ℝ => (Real.exp (-b*t) : ℂ)*
      ∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom t q)
      atTop (𝓝 0) := by
  classical
  apply squeeze_zero_norm' _ (pn_quadratic_exp_gap hgap (xiShiftAbsoluteMass 0))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_left (pn_norm_complement_le Q hβ ht)
    (Real.exp_nonneg _)).trans_eq ?_
  rw [show Real.exp (-b*t)*(xiShiftAbsoluteMass 0*(t^2/2)*Real.exp (β*t)) =
    (xiShiftAbsoluteMass 0*(t^2/2))*(Real.exp (-b*t)*Real.exp (β*t)) by ring,
    ← Real.exp_add]
  congr 2
  ring

private theorem pn_source_split (Q : Set XiZeroCopy) [Fintype Q]
    [DecidablePred (· ∈ Q)] (t : ℝ) :
    liEvenCrossActualClockPrimitive t =
      (∑ q : Q, (liEvenCrossActualClockCosineAtom t q.val).re) +
        (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom t q).re := by
  classical
  have he : liEvenCrossActualClockPrimitive t =
      (∑' q : XiZeroCopy, liEvenCrossActualClockCosineAtom t q).re := by
    simpa only [Complex.ofReal_re] using
      congrArg Complex.re (liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine t)
  rw [he, ← (summable_norm_liEvenCrossActualClockCosineAtom t).of_norm.tsum_subtype_add_tsum_subtype_compl Q,
    Complex.add_re, tsum_fintype]
  congr 1
  · exact map_sum Complex.reAddGroupHom _ _
  · congr 1
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ Q <;> simp [Set.indicator, hq]

/-- Failure of RH gives a full maximal packet and one cofinal clock sequence
with exact normalized primitive limit and unbounded negative primitive values. -/
theorem exists_liEvenCrossActualClockPrimitive_negative_escape_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧ (liEvenCrossActualClockTopPacket b).Finite ∧
      (liEvenCrossActualClockTopPacket b).Nonempty ∧ ∃ t : ℕ → ℝ,
      (∀ n : ℕ, (n : ℝ)+1 ≤ t n) ∧ Tendsto t atTop atTop ∧
      Tendsto (fun n => Real.exp (-b*t n)*liEvenCrossActualClockPrimitive (t n))
        atTop (𝓝 (-(Nat.card (liEvenCrossActualClockTopPacket b) : ℝ)/2)) ∧
      Tendsto (fun n => liEvenCrossActualClockPrimitive (t n)) atTop atBot := by
  classical
  obtain ⟨b, hb, hQfin, hQnonempty, _, β, _, hgap, hβ⟩ :=
    exists_liEvenCrossActualClockTopPacket_of_not_rh hnot
  let Q := liEvenCrossActualClockTopPacket b
  letI : Fintype Q := hQfin.fintype
  letI : Nonempty Q := hQnonempty.to_subtype
  let w : Q → ℂ := fun q => (xiSpectralPoint q.val)⁻¹
  have hw (q : Q) : |(w q).im| = b := q.property
  obtain ⟨t, ht, htcofinal, htop⟩ := pn_finite_negative_limit w hb hw
  have hcompl := (pn_complement_tendsto Q hβ hgap).comp htcofinal
  have htail : Tendsto (fun n => Real.exp (-b*t n)*
      (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom (t n) q).re)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hcompl
  have hlimit : Tendsto (fun n => Real.exp (-b*t n)*liEvenCrossActualClockPrimitive (t n))
      atTop (𝓝 (-(Nat.card Q : ℝ)/2)) := by
    have hsum := htop.add htail
    have heq (n : ℕ) : Real.exp (-b*t n)*liEvenCrossActualClockPrimitive (t n) =
        Real.exp (-b*t n)*(∑ q : Q, (1-Complex.cos ((t n : ℂ)*w q)).re) +
        Real.exp (-b*t n)*
          (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockCosineAtom (t n) q).re := by
      rw [pn_source_split Q (t n)]
      simp only [liEvenCrossActualClockCosineAtom, w, mul_add]
    simpa only [← heq, add_zero, Nat.card_eq_fintype_card] using hsum
  have hcard : 0 < (Nat.card Q : ℝ) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hc : -(Nat.card Q : ℝ)/2 < 0 := by linarith
  have he := Real.tendsto_exp_atTop.comp (htcofinal.const_mul_atTop hb)
  have hp := hlimit.neg_mul_atTop hc he
  refine ⟨b, hb, hQfin, hQnonempty, t, ht, htcofinal, hlimit, hp.congr ?_⟩
  intro n
  calc
    (Real.exp (-b*t n)*liEvenCrossActualClockPrimitive (t n))*Real.exp (b*t n) =
        (Real.exp (-b*t n)*Real.exp (b*t n))*liEvenCrossActualClockPrimitive (t n) := by ring
    _ = liEvenCrossActualClockPrimitive (t n) := by
      rw [← Real.exp_add, show -b*t n+b*t n=0 by ring, Real.exp_zero, one_mul]

private theorem pn_rh_of_eventually_lower (C : ℝ)
    (h : ∀ᶠ t : ℝ in atTop, C ≤ liEvenCrossActualClockPrimitive t) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨_, _, _, _, t, _, htcofinal, _, hnegative⟩ :=
    exists_liEvenCrossActualClockPrimitive_negative_escape_of_not_rh hnot
  obtain ⟨n, hnC, hnlt⟩ :=
    ((htcofinal.eventually h).and (hnegative.eventually (eventually_lt_atBot C))).exists
  exact not_lt_of_ge hnC hnlt

/-- RH is equivalent to nonnegative primitive values on the positive ray,
eventual nonnegativity, or any eventual real lower bound. -/
theorem liEvenCrossActualClockPrimitive_rh_criteria :
    (RiemannHypothesis ↔ ∀ t : ℝ, 0 ≤ t → 0 ≤ liEvenCrossActualClockPrimitive t) ∧
    (RiemannHypothesis ↔ ∀ᶠ t : ℝ in atTop, 0 ≤ liEvenCrossActualClockPrimitive t) ∧
    (RiemannHypothesis ↔ ∃ C : ℝ, ∀ᶠ t : ℝ in atTop, C ≤ liEvenCrossActualClockPrimitive t) := by
  have hforward (hRH : RiemannHypothesis) :
      ∀ᶠ t : ℝ in atTop, 0 ≤ liEvenCrossActualClockPrimitive t :=
    Filter.Eventually.of_forall (liEvenCrossActualClockPrimitive_nonneg_of_rh hRH)
  refine ⟨⟨?_, ?_⟩, ⟨hforward, pn_rh_of_eventually_lower 0⟩, ⟨?_, ?_⟩⟩
  · intro hRH t _
    exact liEvenCrossActualClockPrimitive_nonneg_of_rh hRH t
  · intro h
    apply pn_rh_of_eventually_lower 0
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact h t ht
  · intro hRH
    exact ⟨0, hforward hRH⟩
  · rintro ⟨C, hC⟩
    exact pn_rh_of_eventually_lower C hC

end
end RHTower
