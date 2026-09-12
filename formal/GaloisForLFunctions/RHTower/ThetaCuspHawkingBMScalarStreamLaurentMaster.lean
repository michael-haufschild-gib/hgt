import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamSourceField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMasterCurrent

/-!
# A finite Laurent particular inverse of the scalar–scalar harmonic master source

The original source admits the explicit field `r + A/r + B/r³` at independent parent rate `s`
and output angular eigenvalue `μ`. Its genuine radial derivatives solve `SSMasterEquation`, and
its exterior smoothness supplies the existing seven-row sourced reconstruction interface.

The coefficients require only the angular denominators `2-μ` and `μ-(2s+1)(2s+2)`; the apparent
lower Laurent resonance cancels exactly. Both denominators are discharged for every Xi occurrence,
either physical parent branch, and every independently chosen nonpositive real angular eigenvalue.
The squared cusp principal part also has an explicit nonresonant response at angular shift two.

The reciprocal-radius identity retains the forced growing boundary term and its exact remainder.
Identification with the entire original tensor source, physical boundary admission, and retarded
onset are separate obligations; this particular harmonic inverse does not establish causal action.
-/

open GaloisForLFunctions.HTGeometry.TwistedRadial Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMScalarStream
noncomputable section
set_option autoImplicit false

/-- Coefficient of the third inverse power in the particular master field. -/
def laurentMasterB (s μ : ℂ) : ℂ :=
  s^2*(s+1)^2*(μ-2*s^2-6*s-6)/(8*(2-μ))

/-- The middle coefficient of the original cleared source. -/
def laurentSourceMiddle (s μ : ℂ) : ℂ :=
  -8*s+2*s*μ+s*μ^2-5/2*s^2-9/4*s^2*μ+5/2*s^2*μ^2+
    79/2*s^3-17/2*s^3*μ+54*s^4-29/4*s^4*μ+51/2*s^5+11/2*s^6

/-- Coefficient of the first inverse power, at independent rate and angular eigenvalue. -/
def laurentMasterA (s μ : ℂ) : ℂ :=
  (-laurentSourceMiddle s μ/(2-μ)-6*laurentMasterB s μ)/
    (μ-(2*s+1)*(2*s+2))

/-- Exact decomposition of the original source; the lower apparent resonance cancels. -/
theorem ssMasterSource_laurent (s μ r : ℂ) (hr : r ≠ 0) (hf : r^2-1 ≠ 0)
    (hμ : 2-μ ≠ 0) :
    r^2*(r^2-1)*ssMasterSource s r μ =
      -2*r^3-(μ+2*s-4*s^2)*r+laurentSourceMiddle s μ/((2-μ)*r)-
        (μ-(2*s+3)*(2*s+4))*laurentMasterB s μ/r^3 := by
  unfold ssMasterSource laurentSourceMiddle laurentMasterB
  field_simp
  ring

def laurentMasterField (A B : ℂ) (r : ℝ) : ℂ := (r : ℂ)+A/r+B/(r : ℂ)^3
def laurentMasterFirst (A B : ℂ) (r : ℝ) : ℂ := 1-A/(r : ℂ)^2-3*B/(r : ℂ)^4

theorem hasDerivAt_laurentMasterField (A B : ℂ) {r : ℝ} (hr : (r : ℂ) ≠ 0) :
    HasDerivAt (laurentMasterField A B) (laurentMasterFirst A B r) r := by
  have hR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h := (hR.add ((hasDerivAt_const r A).div hR hr)).add
    ((hasDerivAt_const r B).div (hR.pow 3) (pow_ne_zero 3 hr))
  refine h.congr_deriv ?_
  simp only [laurentMasterFirst, Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_laurentMasterFirst (A B : ℂ) {r : ℝ} (hr : (r : ℂ) ≠ 0) :
    HasDerivAt (laurentMasterFirst A B) (2*A/(r : ℂ)^3+12*B/(r : ℂ)^5) r := by
  have hR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h := (((hasDerivAt_const r A).div (hR.pow 2) (pow_ne_zero 2 hr)).const_sub 1).sub
    ((hasDerivAt_const r (3*B)).div (hR.pow 4) (pow_ne_zero 4 hr))
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The actual twisted operator on a finite Laurent field. -/
theorem laurentMasterField_operator (s μ A B : ℂ) {r : ℝ} (hr1 : 1 < r) :
    (r : ℂ)^2*((r : ℂ)^2-1)*
      (twist s (twist s (laurentMasterField A B)) r+
        2*r/((r : ℂ)^2-1)*twist s (laurentMasterField A B) r+
        (μ/((r : ℂ)^2*((r : ℂ)^2-1))-4*s^2/((r : ℂ)^2-1)^2)*laurentMasterField A B r) =
      2*(r : ℂ)^3+(μ+2*s-4*s^2)*r+
        ((μ-(2*s+1)*(2*s+2))*A+6*B)/r+
        (μ-(2*s+3)*(2*s+4))*B/(r : ℂ)^3 := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  have he : ∀ᶠ t in 𝓝 r, HasDerivAt (laurentMasterField A B) (laurentMasterFirst A B t) t := by
    filter_upwards [exterior_eventually hr1] with t ht
    exact hasDerivAt_laurentMasterField A B (exterior_ne t ht).1
  have ht := hasDerivAt_twist s hr hf he (hasDerivAt_laurentMasterFirst A B hr)
  rw [twist, ht.deriv]
  simp only [twist, (hasDerivAt_laurentMasterField A B hr).deriv,
    laurentMasterFirst, laurentMasterField]
  field_simp
  ring

/-- An explicit particular master field for independent source rate and output eigenvalue. -/
def ssLaurentMaster (s μ : ℂ) : ℝ → ℂ :=
  laurentMasterField (laurentMasterA s μ) (laurentMasterB s μ)

theorem ssLaurentMaster_equation (s μ : ℂ) (hμ : 2-μ ≠ 0)
    (hres : μ-(2*s+1)*(2*s+2) ≠ 0) : SSMasterEquation s μ (ssLaurentMaster s μ) := by
  intro r hr1
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  have ho := laurentMasterField_operator s μ (laurentMasterA s μ) (laurentMasterB s μ) hr1
  have hs := ssMasterSource_laurent s μ r hr hf hμ
  have hA : (μ-(2*s+1)*(2*s+2))*laurentMasterA s μ+6*laurentMasterB s μ =
      -laurentSourceMiddle s μ/(2-μ) := by
    unfold laurentMasterA
    rw [mul_div_cancel₀ _ hres]
    ring
  rw [hA] at ho
  change _ + ssMasterSource s r μ = 0
  apply (mul_eq_zero.mp (show (r : ℂ)^2*((r : ℂ)^2-1)*
      (twist s (twist s (ssLaurentMaster s μ)) r+2*r/((r : ℂ)^2-1)*twist s (ssLaurentMaster s μ) r+
        (μ/((r : ℂ)^2*((r : ℂ)^2-1))-4*s^2/((r : ℂ)^2-1)^2)*ssLaurentMaster s μ r+
        ssMasterSource s r μ) = 0 from ?_)).resolve_left (mul_ne_zero (pow_ne_zero 2 hr) hf)
  rw [mul_add, show ssLaurentMaster s μ = laurentMasterField (laurentMasterA s μ) (laurentMasterB s μ) from rfl, ho, hs]
  field_simp
  ring

/-- The particular field is smooth on the entire exterior. -/
theorem ssLaurentMaster_contDiffOn (s μ : ℂ) :
    ContDiffOn ℝ ∞ (ssLaurentMaster s μ) (Ioi 1) := by
  have hi : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ)) (Ioi 1) := contDiff_ofReal_real.contDiffOn
  have hn : ∀ r ∈ Ioi (1 : ℝ), (r : ℂ) ≠ 0 := fun r hr => (exterior_ne r hr).1
  have hA : ContDiffOn ℝ ∞ (fun _ : ℝ => laurentMasterA s μ) (Ioi 1) := contDiffOn_const
  have hB : ContDiffOn ℝ ∞ (fun _ : ℝ => laurentMasterB s μ) (Ioi 1) := contDiffOn_const
  change ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ)+laurentMasterA s μ/(r : ℂ)+
    laurentMasterB s μ/(r : ℂ)^3) (Ioi 1)
  simpa only [div_eq_mul_inv,Pi.inv_apply] using (hi.add (hA.mul (hi.inv hn))).add
    (hB.mul ((hi.pow 3).inv (fun r hr => pow_ne_zero 3 (hn r hr))))

/-- All source and reconstruction regularity is supplied by the explicit particular field. -/
theorem ssLaurentMaster_sourcedData (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-(2*s+1)*(2*s+2) ≠ 0) :
    SourcedMasterData s μ (ssLaurentMaster s μ)
      (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ) :=
  ssSourcedMasterData s μ hs hμ _ (ssLaurentMaster_contDiffOn s μ)
    (ssLaurentMaster_equation s μ hμ hres)

/-- Only the two already occurring angular resolvents are required by the first coefficient. -/
theorem laurentMasterA_resolvents (s μ : ℂ) (hμ : 2-μ ≠ 0)
    (hres : μ-(2*s+1)*(2*s+2) ≠ 0) :
    laurentMasterA s μ = s*(5*s+2)/2+s^2*(s+1)*(s+2)/(2-μ)+
      (3*s*(s+1)^2*(3*s+4))/(2*(μ-(2*s+1)*(2*s+2))) := by
  unfold laurentMasterA
  generalize hd : μ-(2*s+1)*(2*s+2) = d at hres ⊢
  field_simp [hres,hμ]
  rw [← hd]
  unfold laurentSourceMiddle laurentMasterB
  field_simp
  ring

/-- The third inverse-power coefficient needs only the angular inverse at two. -/
theorem laurentMasterB_resolvent (s μ : ℂ) (hμ : 2-μ ≠ 0) :
    laurentMasterB s μ = -s^2*(s+1)^2/8-s^2*(s+1)^3*(s+2)/(4*(2-μ)) := by
  unfold laurentMasterB
  field_simp
  ring

/-- The source-forced boundary term and its entire decaying remainder, exactly. -/
theorem ssLaurentMaster_reciprocal (s μ : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ)*ssLaurentMaster s μ x⁻¹ =
      1+laurentMasterA s μ*(x : ℂ)^2+laurentMasterB s μ*(x : ℂ)^4 ∧
    ssLaurentMaster s μ x⁻¹-(x : ℂ)⁻¹ =
      laurentMasterA s μ*x+laurentMasterB s μ*(x : ℂ)^3 := by
  have hc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  simp only [ssLaurentMaster,laurentMasterField,Complex.ofReal_inv]
  constructor <;> field_simp
  all_goals ring

/-- Independent real angular eigenvalues do not meet the remaining Laurent pole
for a non-real rate to the left of minus one. -/
theorem laurentPole_ne_zero (s : ℂ) (hs : s.re < -1) (hi : s.im ≠ 0) (μ : ℝ) :
    (μ : ℂ)-(2*s+1)*(2*s+2) ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  have he : ((μ : ℂ)-(2*s+1)*(2*s+2)).im = -(8*s.re+6)*s.im := by
    norm_num [Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.add_re,Complex.add_im]
    ring
  rw [he,Complex.zero_im] at hh
  have hz := (mul_eq_zero.mp hh).resolve_right hi
  linarith

/-- The two physical branches satisfy the Laurent pole exclusion conditions unconditionally. -/
theorem physicalLaurentRate_bounds (q : XiZeroCopy) (branch : Bool) :
    (D4BMModularCore.physicalRate q branch).re < -1 ∧
      (D4BMModularCore.physicalRate q branch).im ≠ 0 := by
  have hr := xi_divisor_support_re_mem_open_unit q.1
  have hi := xi_divisor_support_im_ne_zero q.1
  cases branch <;> norm_num [D4BMModularCore.physicalRate,Complex.sub_re,Complex.sub_im]
  · exact ⟨by linarith [hr.1], hi⟩
  · exact ⟨by linarith [hr.2], hi⟩

/-- Every actual Xi occurrence and either physical branch has the explicit particular
response at every independently chosen nonpositive real angular eigenvalue. -/
theorem physical_ssLaurentMaster_sourcedData (q : XiZeroCopy) (branch : Bool) (k : ℝ) :
    SourcedMasterData (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2)
      (ssLaurentMaster (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcTT (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcTR (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcRR (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcT (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcR (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcTF (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2))
      (srcL (D4BMModularCore.physicalRate q branch) (-(k : ℂ)^2)) := by
  obtain ⟨hr,hi⟩ := physicalLaurentRate_bounds q branch
  have hs : D4BMModularCore.physicalRate q branch ≠ 0 := by
    intro h
    exact hi (congrArg Complex.im h)
  have hμ : (2 : ℂ)-(-(k : ℂ)^2) ≠ 0 := by
    exact_mod_cast (show (2 : ℝ)-(-k^2) ≠ 0 by nlinarith [sq_nonneg k])
  have hp := laurentPole_ne_zero (D4BMModularCore.physicalRate q branch) hr hi (-k^2)
  push_cast at hp
  exact ssLaurentMaster_sourcedData _ _ hs hμ hp

/-- None of the three original squared cusp powers is resonant at the angular shift two. -/
theorem xi_cusp_two_denominators (q : XiZeroCopy) :
    (2*(q.1 : ℂ))*(2*(q.1 : ℂ)-1)-2 ≠ 0 ∧
      (2-2*(q.1 : ℂ))*(1-2*(q.1 : ℂ))-2 ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have hlinear (a b : ℝ) (ha : a ≠ 0) : (a : ℂ)*(q.1 : ℂ)+(b : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    norm_num [Complex.mul_im] at hh
    exact hi (hh.resolve_left ha)
  have hq : (q.1 : ℂ) ≠ 0 := by simpa using hlinear 1 0 (by norm_num)
  have hm : (q.1 : ℂ)-1 ≠ 0 := by simpa only [Complex.ofReal_one,one_mul,Complex.ofReal_neg,sub_eq_add_neg] using hlinear 1 (-1) (by norm_num)
  have hp : 2*(q.1 : ℂ)+1 ≠ 0 := by simpa using hlinear 2 1 (by norm_num)
  have ht : 2*(q.1 : ℂ)-3 ≠ 0 := by simpa [sub_eq_add_neg] using hlinear 2 (-3) (by norm_num)
  constructor
  · rw [show (2*(q.1 : ℂ))*(2*(q.1 : ℂ)-1)-2 =
      2*((q.1 : ℂ)-1)*(2*(q.1 : ℂ)+1) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) hp
  · rw [show (2-2*(q.1 : ℂ))*(1-2*(q.1 : ℂ))-2 =
      2*(q.1 : ℂ)*(2*(q.1 : ℂ)-3) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hq) ht

/-- The full squared cusp principal part, including the cross term, has an explicit
response at the second angular parameter needed by the Laurent construction. -/
theorem xi_cusp_two_response_equation (q : XiZeroCopy) (A D : ℂ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    D4BMAngularSeries.hyperbolicLaplacian (D4BMQuadraticMixedSource.cuspPowerResponse 2 (q.1 : ℂ) A D) z-
      2*D4BMQuadraticMixedSource.cuspPowerResponse 2 (q.1 : ℂ) A D z =
      (A*(z 1 : ℂ)^(q.1 : ℂ)+D*(z 1 : ℂ)^(1-(q.1 : ℂ)))^2 := by
  obtain ⟨h0,h2⟩ := xi_cusp_two_denominators q
  exact D4BMQuadraticMixedSource.cusp_response_equation 2 (q.1 : ℂ) A D z hz h0 (by norm_num) h2
end
end RHTower.D4BMScalarStream
