import GaloisForLFunctions.RHTower.EulerDeletionReflectedCurrentEnergy
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

/-!
# Completion transport of the full deletion chronology

The full complex second level has an explicit harmonic finite part throughout
the strip. Scalar completion changes both its divergent coefficient and its
finite phase response. The actual xi endpoint completion is included.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCompletedChronology
open DeletionReflectedGram DeletionReflectedCurrent DeletionReflectedEnergy
open DeletionChronologicalLimit DeletionJointCirculation

/-- The retained imaginary Abel response of the literal source. -/
def abelPhase (p : ℕ) (s : ℂ) : ℝ := -(∑' n, abelRemainder p p s n).im

/-- The exact harmonic counterterm for a single chronological order. -/
def harmonicCounterterm (p N : ℕ) : ℂ :=
  ((DeletionReflectedGram.residue (p+1) (p+1)*(harmonic N:ℝ)/2:ℝ):ℂ)

/-- A single chronological order, retaining its full complex finite part. -/
def renormalizedPrefix (p : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  reflectedCross p p s N+harmonicCounterterm p N

/-- Explicit finite value; endpoint, reflection energy, and Abel phase are all retained. -/
def chronologyLimit (p : ℕ) (s : ℂ) : ℂ :=
  (((eulerDeletionDirichletSum p s*star (eulerDeletionDirichletSum p (partner s))).re-
    finitePart (p+1) (p+1)-(reflectionCurrent p s).re)/2:ℝ)+
    (abelPhase p s:ℂ)*Complex.I

private theorem partner_strip {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    0<(partner s).re ∧ (partner s).re<1 := by
  simp only [partner, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  constructor <;> linarith

private theorem arithmetic_im_zero (p N : ℕ) :
    (∑ n ∈ Finset.range (N-1),
      coprimeAbelCoefficient (p+1) (p+1) (n+1)/((n+1:ℕ):ℂ)).im=0 := by
  simp [coprimeAbelCoefficient, Complex.div_im]

/-- The imaginary chronological part converges without any logarithmic subtraction. -/
theorem reflectedCross_im_tendsto (p : ℕ) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (fun N => (reflectedCross p p s N).im) atTop (nhds (abelPhase p s)) := by
  have hb := (Complex.continuous_im.tendsto _).comp (terminal_tendsto p p hs hs')
  have hr := ((abelRemainder_summable_norm p p hs hs').of_norm.hasSum.tendsto_sum_nat).comp
    (Filter.tendsto_sub_atTop_nat 1)
  have hi := (Complex.continuous_im.tendsto _).comp hr
  have ht := hb.sub hi
  change Tendsto (fun N => (terminal p p s N).im-
    (∑ n ∈ Finset.range (N-1), abelRemainder p p s n).im) atTop
    (nhds ((0:ℂ).im-(∑' n, abelRemainder p p s n).im)) at ht
  simpa only [Complex.zero_im, zero_sub, abelPhase] using ht.congr (fun N => by
    rw [reflectedCross_abel, Complex.sub_im, Complex.sub_im, arithmetic_im_zero, sub_zero])

/-- Complete complex harmonic normalization, valid throughout the open strip. -/
theorem renormalizedPrefix_tendsto (p : ℕ) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (renormalizedPrefix p s) atTop (nhds (chronologyLimit p s)) := by
  have hr := partner_strip hs hs'
  have hsym := (Complex.continuous_re.tendsto _).comp (symmetricCross_harmonic_tendsto p p hs hs')
  have hvar := (Complex.continuous_re.tendsto _).comp
    (variationCurrent_tendsto p p hs hs' hr.1 hr.2).2
  have hre := (hsym.add hvar).div_const 2
  have he (N : ℕ) :
      ((symmetricCross p p s N+
        (DeletionReflectedGram.residue (p+1) (p+1)*(harmonic N:ℝ):ℂ)).re+
        (reflectedCross p p s N-reflectedCross p p (partner s) N).re)/2 =
      (renormalizedPrefix p s N).re := by
    simp [renormalizedPrefix, harmonicCounterterm, symmetricCross, reflectedCross,
      partner_partner]
    ring
  have hre' : Tendsto (fun N => (renormalizedPrefix p s N).re) atTop
      (nhds (((eulerDeletionDirichletSum p s*
        star (eulerDeletionDirichletSum p (partner s))).re-
        finitePart (p+1) (p+1)-(reflectionCurrent p s).re)/2)) := by
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re, reflectionCurrent,
      sub_eq_add_neg, Complex.add_re] using hre.congr he
  have him : Tendsto (fun N => (renormalizedPrefix p s N).im) atTop (nhds (abelPhase p s)) := by
    simpa only [renormalizedPrefix, harmonicCounterterm, Complex.add_im,
      Complex.ofReal_im, add_zero] using reflectedCross_im_tendsto p hs hs'
  exact (hre'.ofReal.add (him.ofReal.mul_const Complex.I)).congr
    (fun N => Complex.re_add_im (renormalizedPrefix p s N))

/-- The subtraction between the two finite values is exactly the full source current. -/
theorem chronologyLimit_sub_partner (p : ℕ) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    chronologyLimit p s-chronologyLimit p (partner s) = -reflectionCurrent p s := by
  have hr := partner_strip hs hs'
  have h := (renormalizedPrefix_tendsto p hs hs').sub (renormalizedPrefix_tendsto p hr.1 hr.2)
  have hv := (variationCurrent_tendsto p p hs hs' hr.1 hr.2).2
  exact tendsto_nhds_unique (h.congr (fun N => by simp [renormalizedPrefix])) hv

/-- The imaginary finite part agrees at the two actual zero partners. -/
theorem abelPhase_partner_at_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    abelPhase p (partner rho.1)=abelPhase p rho.1 := by
  have h := congrArg Complex.im (chronologyLimit_sub_partner p
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    (RiemannGaussian.NontrivialZetaZero.re_lt_one rho))
  simp only [chronologyLimit, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_one,
    mul_zero, zero_add, add_zero, Complex.neg_im,
    reflectionCurrent_im_at_nontrivial_zero p rho, neg_zero] at h
  linarith

/-- At actual zeros the real finite part is exactly the arithmetic constant plus signed energy. -/
theorem chronologyLimit_at_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    chronologyLimit p rho.1 =
      ((-finitePart (p+1) (p+1)-(reflectionCurrent p rho.1).re)/2:ℝ)+
        (abelPhase p rho.1:ℂ)*Complex.I := by
  rw [chronologyLimit, source_endpoint_value p
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) rho.2.2.2,
    rho.2.1, mul_zero, zero_mul, Complex.zero_re, zero_sub]

/-- Scalar completion acts on the literal finite chronological pairing by its full complex product. -/
theorem chronologicalCrossPrefix_scale (a b : ℂ) (u v : ℕ → ℂ) (N : ℕ) :
    chronologicalCrossPrefix (fun n => a*u n) (fun n => b*v n) N =
      (a*star b)*chronologicalCrossPrefix u v N := by
  simp only [chronologicalCrossPrefix, chronologicalCrossTerm, ← Finset.mul_sum, star_mul']
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum]
  ring

/-- The completed reflected difference with the exact induced harmonic subtraction. -/
def completedDifference (a b : ℂ) (p : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  chronologicalCrossPrefix (fun n => a*eulerDeletionWeightedJump p s n)
      (fun n => b*eulerDeletionWeightedJump p (partner s) n) N-
    chronologicalCrossPrefix (fun n => b*eulerDeletionWeightedJump p (partner s) n)
      (fun n => a*eulerDeletionWeightedJump p s n) N+
    (a*star b-star (a*star b))*harmonicCounterterm p N

/-- Every cutoff retains precisely the divergence created by the completion phase. -/
theorem completedDifference_eq (a b : ℂ) (p : ℕ) (s : ℂ) (N : ℕ) :
    completedDifference a b p s N =
      (a*star b)*renormalizedPrefix p s N-
        star (a*star b)*renormalizedPrefix p (partner s) N := by
  simp only [completedDifference, chronologicalCrossPrefix_scale, renormalizedPrefix,
    reflectedCross, partner_partner, star_mul', star_star]
  ring

/-- Full complex completion transport holds on the entire open strip. -/
theorem completedDifference_tendsto (a b : ℂ) (p : ℕ) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (completedDifference a b p s) atTop
      (nhds ((a*star b)*chronologyLimit p s-
        star (a*star b)*chronologyLimit p (partner s))) := by
  have hr := partner_strip hs hs'
  exact (((renormalizedPrefix_tendsto p hs hs').const_mul (a*star b)).sub
    ((renormalizedPrefix_tendsto p hr.1 hr.2).const_mul (star (a*star b)))).congr
      (fun N => (completedDifference_eq a b p s N).symm)

/-- The unrenormalized difference, with the completion-induced counterterm removed. -/
def ordinaryDifference (a b : ℂ) (p : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  completedDifference a b p s N-(a*star b-star (a*star b))*harmonicCounterterm p N

/-- Ordinary convergence survives scalar completion exactly when its cross phase is real. -/
theorem ordinaryDifference_converges_iff (a b : ℂ) {p : ℕ} (hp : 0<p) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) :
    (∃ L : ℂ, Tendsto (ordinaryDifference a b p s) atTop (nhds L)) ↔
      (a*star b).im=0 := by
  have hc := completedDifference_tendsto a b p hs hs'
  constructor
  · rintro ⟨L,hL⟩
    have hd := hc.sub hL
    have hi := ((Complex.continuous_im.tendsto _).comp hd).div_atTop
      GaloisForLFunctions.tendsto_harmonic_cast_atTop
    have he : Tendsto (fun _ : ℕ => (a*star b).im*(p:ℝ)) atTop (nhds 0) := by
      refine hi.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hh : (harmonic N:ℝ)≠0 := by exact_mod_cast (harmonic_pos (by omega : N≠0)).ne'
      dsimp only [Function.comp_def]
      simp only [ordinaryDifference, harmonicCounterterm, sub_sub_cancel,
        DeletionReflectedGram.residue, Nat.gcd_self, Nat.cast_add, Nat.cast_one,
        add_sub_cancel_right, Complex.mul_im, Complex.sub_im, Complex.star_def,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
      field_simp
      ring
    have hz : (a*star b).im*(p:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds he
    exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast hp.ne')
  · intro h
    have hk : a*star b-star (a*star b)=0 := by
      apply sub_eq_zero.mpr
      apply Complex.ext
      · rfl
      · change (a*star b).im = -(a*star b).im
        rw [h, neg_zero]
    refine ⟨(a*star b)*chronologyLimit p s-star (a*star b)*chronologyLimit p (partner s), ?_⟩
    exact hc.congr (fun N => by simp only [ordinaryDifference, hk, zero_mul, sub_zero])

/-- Exact completion law at every actual zero, including its independent phase response. -/
theorem completed_value_at_zero (a b : ℂ) (p : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    (a*star b)*chronologyLimit p rho.1-
      star (a*star b)*chronologyLimit p (partner rho.1) =
      (-(a*star b).re*(reflectionCurrent p rho.1).re-
        2*(a*star b).im*abelPhase p rho.1:ℝ)-
      ((a*star b).im*finitePart (p+1) (p+1):ℝ)*Complex.I := by
  have hp := chronologyLimit_at_zero p (RiemannGaussian.NontrivialZetaZero.conjugatePartner rho)
  change chronologyLimit p (partner rho.1) = _ at hp
  rw [chronologyLimit_at_zero p rho, hp]
  change _ = _
  simp only [show (RiemannGaussian.NontrivialZetaZero.conjugatePartner rho).1 =
      partner rho.1 from rfl, reflectionCurrent_partner, Complex.neg_re,
    abelPhase_partner_at_zero]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The literal factor completing each deletion endpoint to the entire xi normalization. -/
def xiFactor (p : ℕ) (s : ℂ) : ℂ :=
  s*(1-s)*Complex.Gammaℝ s/(1-complexEulerDilationFactor (p+1) s)

/-- The actual xi factor is nonzero throughout the open strip for every nontrivial channel. -/
theorem xiFactor_ne_zero {p : ℕ} (hp : 0<p) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) : xiFactor p s ≠ 0 := by
  have hs0 : s≠0 := by intro h; subst s; norm_num at hs
  have hs1 : s≠1 := by intro h; subst s; norm_num at hs'
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1.symm))
    (RiemannGaussian.Gammaℝ_ne_zero_of_re_pos hs)) (one_sub_dilation_ne_zero (by omega) hs')

/-- Actual completion identity, proved from the literal deletion endpoint and gamma factor. -/
theorem xiFactor_mul_endpoint {p : ℕ} (hp : 0<p) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) :
    xiFactor p s*eulerDeletionDirichletSum p s=RiemannGaussian.riemannXi s := by
  have hs1 : s≠1 := by intro h; subst s; norm_num at hs'
  rw [source_endpoint_value p hs hs1,
    RiemannGaussian.riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs hs1, xiFactor]
  field_simp [one_sub_dilation_ne_zero (p := p+1) (by omega) hs']

/-- The finite completed arithmetic prefixes converge to the genuine entire xi endpoint. -/
theorem xi_completed_endpoint_tendsto {p : ℕ} (hp : 0<p) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (endpoint (fun n => xiFactor p s*eulerDeletionWeightedJump p s n))
      atTop (nhds (RiemannGaussian.riemannXi s)) := by
  have ht := (source_endpoint_tendsto p hs).const_mul (xiFactor p s)
  rw [xiFactor_mul_endpoint hp hs hs'] at ht
  change Tendsto (fun N => ∑ n ∈ Finset.range N, xiFactor p s*eulerDeletionWeightedJump p s n)
    atTop (nhds (RiemannGaussian.riemannXi s))
  simpa only [endpoint, Finset.mul_sum] using ht

/-- The exact two-channel phase multiplying the xi-completed chronology. -/
def xiPhase (p : ℕ) (s : ℂ) : ℂ := xiFactor p s*star (xiFactor p (partner s))

/-- The actual xi-completed current has the explicit harmonic-normalized source limit. -/
theorem xi_completedDifference_at_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (completedDifference (xiFactor p rho.1) (xiFactor p (partner rho.1)) p rho.1)
      atTop (nhds (((-(xiPhase p rho.1).re*(reflectionCurrent p rho.1).re-
        2*(xiPhase p rho.1).im*abelPhase p rho.1:ℝ):ℂ)-
        ((xiPhase p rho.1).im*finitePart (p+1) (p+1):ℝ)*Complex.I)) := by
  have ht := completedDifference_tendsto (xiFactor p rho.1) (xiFactor p (partner rho.1)) p
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)
  rwa [completed_value_at_zero] at ht

/-- Modulus two has no finite arithmetic constant, but still retains the full completion-phase term. -/
theorem xi_modulus_two_completedDifference_at_zero (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (completedDifference (xiFactor 1 rho.1) (xiFactor 1 (partner rho.1)) 1 rho.1)
      atTop (nhds ((-(xiPhase 1 rho.1).re*(reflectionCurrent 1 rho.1).re-
        2*(xiPhase 1 rho.1).im*abelPhase 1 rho.1:ℝ):ℂ)) := by
  have hk : finitePart 2 2=0 := by norm_num [finitePart]; ring
  simpa only [show 1+1=2 from rfl, hk, mul_zero, Complex.ofReal_zero, zero_mul, sub_zero] using
    xi_completedDifference_at_zero 1 rho

end RHTower.DeletionCompletedChronology
end
