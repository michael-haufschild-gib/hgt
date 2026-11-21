import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanKernel

/-!
# Logarithmic distortion of the hyperbolic point-pair and Bergman factors

The logarithmic distortion estimate of Koskela et al., Lemma 2.3, has
an exact point-pair analogue. Moving the endpoints costs the sum of their
hyperbolic distances, with coefficient one for the point-pair factor and
one half for the normalized Bergman factor. Positivity preserves the
same multiplicative comparison on periodization.
-/

open UpperHalfPlane Filter
open scoped MatrixGroups
noncomputable section
namespace GaloisForLFunctions.CompactHyperbolicSurfaces
open GaloisForLFunctions.HTGeometry

private theorem distance_pair {z w Z W : ℍ} :
    dist z w ≤ dist Z W + (dist z Z + dist w W) := by
  have h := dist_triangle4 z Z W w
  rw [dist_comm W w] at h
  linarith only [h]

/-- The multiplicative distortion has no prefactor, including at zero
displacement. The two endpoints may move different distances. -/
theorem one_add_pairU_transport (z w Z W : ℍ) :
    1+pairU z w ≤ Real.exp (dist z Z + dist w W)*(1+pairU Z W) := by
  let D := dist z Z + dist w W
  have hd : 0 ≤ D := add_nonneg dist_nonneg dist_nonneg
  have ha : dist z w ≤ D+dist Z W := by linarith only [distance_pair (z:=z) (w:=w) (Z:=Z) (W:=W)]
  have hb : -dist z w ≤ D-dist Z W := by
    have h := distance_pair (z:=Z) (w:=W) (Z:=z) (W:=w)
    rw [dist_comm Z z,dist_comm W w] at h
    linarith only [h]
  have he := Real.exp_le_exp.mpr ha
  have hf := Real.exp_le_exp.mpr hb
  rw [Real.exp_add] at he
  rw [sub_eq_add_neg,Real.exp_add] at hf
  have h1 := Real.one_le_exp hd
  change 1+pairU z w ≤ Real.exp D*(1+pairU Z W)
  rw [pairU_eq_cosh,pairU_eq_cosh,Real.cosh_eq,Real.cosh_eq]
  linarith only [he,hf,h1]

private theorem log_pair_one_sided (z w Z W : ℍ) :
    Real.log (1+pairU z w)-Real.log (1+pairU Z W) ≤ dist z Z+dist w W := by
  have h₀ : 0 < 1+pairU z w := by linarith only [pairU_nonneg z w]
  have h₁ : 0 < 1+pairU Z W := by linarith only [pairU_nonneg Z W]
  have hh := Real.log_le_log h₀ (one_add_pairU_transport z w Z W)
  rw [Real.log_mul (Real.exp_ne_zero _) h₁.ne',Real.log_exp] at hh
  linarith only [hh]

/-- The logarithm of the exact positive point-pair weight is Lipschitz
in the sum of the hyperbolic endpoint distances. -/
theorem log_pairU_distortion (z w Z W : ℍ) :
    |Real.log (1+pairU z w)-Real.log (1+pairU Z W)| ≤ dist z Z+dist w W := by
  have h := log_pair_one_sided Z W z w
  rw [dist_comm Z z,dist_comm W w] at h
  exact abs_le.mpr ⟨by linarith only [h],log_pair_one_sided z w Z W⟩

/-- Normalization of the Bergman factor divides its logarithmic
displacement cost by two. -/
theorem log_bergK_distortion (z w Z W : ℍ) :
    |Real.log ‖bergK z w‖ - Real.log ‖bergK Z W‖| ≤ (dist z Z+dist w W)/2 := by
  have lognorm (a b : ℍ) : 2*Real.log ‖bergK a b‖ = -Real.log (1+pairU a b) := by
    have hh := congrArg Real.log (norm_bergK_sq a b)
    simpa only [Real.log_pow,Real.log_inv,Nat.cast_ofNat] using hh
  have h := abs_le.mp (log_pairU_distortion z w Z W)
  apply abs_le.mpr
  constructor <;> linarith only [h.1,h.2,lognorm z w,lognorm Z W]

/-- Every positive inverse-power automorphic kernel satisfies the same
global distortion law as its individual orbit terms. -/
theorem automorphic_power_transport {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ)
    {σ : ℝ} (hσ : 1 < σ) (z w Z W : ℍ) :
    autR Γ (fun u => (1+u)^(-σ)) z w ≤
      Real.exp (σ*(dist z Z+dist w W))*autR Γ (fun u => (1+u)^(-σ)) Z W := by
  let D := dist z Z+dist w W
  unfold autR
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hΓ.summable_rpow hσ z w) ((hΓ.summable_rpow hσ Z W).mul_left _)
  intro g
  let a := 1+pairU z ((g:SL(2, ℝ)) • w)
  let b := 1+pairU Z ((g:SL(2, ℝ)) • W)
  have ha : 0 < a := by dsimp only [a]; linarith only [pairU_nonneg z ((g:SL(2, ℝ)) • w)]
  have hb : 0 < b := by dsimp only [b]; linarith only [pairU_nonneg Z ((g:SL(2, ℝ)) • W)]
  have h := log_pair_one_sided Z ((g:SL(2, ℝ)) • W) z ((g:SL(2, ℝ)) • w)
  rw [dist_smul,dist_comm Z z,dist_comm W w] at h
  change Real.log b - Real.log a ≤ D at h
  change a^(-σ) ≤ Real.exp (σ*D)*b^(-σ)
  rw [Real.rpow_def_of_pos ha,Real.rpow_def_of_pos hb,← Real.exp_add,Real.exp_le_exp]
  linarith only [mul_le_mul_of_nonneg_left h (by linarith only [hσ] : 0 ≤ σ)]

/-- Squared hyperbolic half-angle gives the exact normalized point-pair factor. -/
theorem one_add_pairU_half_angle (z w : ℍ) :
    1+pairU z w = Real.cosh (dist z w/2)^2 := by
  have h := Real.cosh_two_mul (dist z w/2)
  rw [show 2*(dist z w/2)=dist z w by ring] at h
  rw [pairU_eq_cosh,h]
  linarith only [Real.cosh_sq_sub_sinh_sq (dist z w/2)]

/-- Largest multiplicative change from a pair initially separated by
`r`, when the two endpoints move a total distance at most `D`. -/
def radialTransport (r D : ℝ) := (Real.cosh ((r+D)/2)/Real.cosh (r/2))^2

theorem radialTransport_half_angle (r D : ℝ) :
    radialTransport r D=(Real.cosh (D/2)+Real.tanh (r/2)*Real.sinh (D/2))^2 := by
  unfold radialTransport
  rw [add_div,Real.cosh_add,Real.tanh_eq_sinh_div_cosh]
  congr 1
  field_simp [(Real.cosh_pos (r/2)).ne']

theorem pairU_radial_transport (z w Z W : ℍ) {D : ℝ} (hD : dist z Z+dist w W≤D) :
    1+pairU z w ≤ radialTransport (dist Z W) D*(1+pairU Z W) := by
  have h := (distance_pair (z:=z) (w:=w) (Z:=Z) (W:=W)).trans (add_le_add le_rfl hD)
  have ha := Real.cosh_strictMonoOn.monotoneOn (show 0≤dist z w/2 by positivity)
      (show 0≤(dist Z W+D)/2 by linarith only [h,show 0≤dist z w from dist_nonneg])
      (div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤2))
  rw [one_add_pairU_half_angle,one_add_pairU_half_angle,radialTransport,div_pow,
    div_mul_cancel₀ _ (pow_ne_zero 2 (Real.cosh_pos _).ne')]
  exact pow_le_pow_left₀ (Real.cosh_pos _).le ha 2

private def verticalPoint (t : ℝ) : ℍ := ⟨⟨0,Real.exp t⟩,Real.exp_pos t⟩

private theorem vertical_distance (r t : ℝ) : dist (verticalPoint r) (verticalPoint t)=|r-t| :=
  (UpperHalfPlane.isometry_vertical_line 0).dist_eq r t

/-- A single vertical geodesic realizes the finite-radius envelope for
every prescribed initial separation and every displacement. -/
theorem radial_transport_attained {r D : ℝ} (hr : 0≤r) (hD : 0≤D) :
    ∃ z w Z W : ℍ, dist Z W=r ∧ dist z Z+dist w W=D ∧
      1+pairU z w=radialTransport r D*(1+pairU Z W) := by
  let o := verticalPoint 0
  let a := verticalPoint r
  let b := verticalPoint (r+D)
  have ha : dist a o = r := by rw [vertical_distance,sub_zero,abs_of_nonneg hr]
  have hb : dist b o = r+D := by rw [vertical_distance,sub_zero,abs_of_nonneg (add_nonneg hr hD)]
  have hba : dist b a = D := by rw [vertical_distance,add_sub_cancel_left,abs_of_nonneg hD]
  refine ⟨b,o,a,o,ha,by rw [hba,dist_self,add_zero],?_⟩
  rw [one_add_pairU_half_angle,one_add_pairU_half_angle,ha,hb,radialTransport,div_pow,
    div_mul_cancel₀ _ (pow_ne_zero 2 (Real.cosh_pos _).ne')]

private theorem radial_transport_limit (D : ℝ) :
    Filter.Tendsto (fun r => radialTransport r D) Filter.atTop (nhds (Real.exp D)) := by
  have expdec := Real.tendsto_exp_neg_atTop_nhds_zero
  have ht : Filter.Tendsto (fun r : ℝ => Real.tanh (r/2)) Filter.atTop (nhds 1) := by
    have rat := ((tendsto_const_nhds (x := (1:ℝ))).sub expdec).div ((tendsto_const_nhds (x := (1:ℝ))).add expdec)
      (by norm_num : (1:ℝ)+0≠0)
    have eq (r : ℝ) : Real.tanh (r/2)=(1-Real.exp (-r))/(1+Real.exp (-r)) := by
      have prod : Real.exp (r/2)*Real.exp (-(r/2))=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
      have ee : Real.exp (-r)=Real.exp (-(r/2))*Real.exp (-(r/2)) := by
        rw [←Real.exp_add]; congr 1; ring
      rw [Real.tanh_eq_sinh_div_cosh,ee]
      apply (div_eq_div_iff (Real.cosh_pos _).ne' (by positivity)).mpr
      rw [Real.sinh_eq,Real.cosh_eq]
      linear_combination Real.exp (-(r/2))*prod
    have rat' : Filter.Tendsto (fun r : ℝ => (1-Real.exp (-r))/(1+Real.exp (-r))) Filter.atTop (nhds 1) := by
      simpa only [sub_zero,add_zero,div_one,Pi.div_def] using rat
    exact rat'.congr fun r => (eq r).symm
  have limit := ((ht.mul_const (Real.sinh (D/2))).const_add (Real.cosh (D/2))).pow 2
  have ee : (Real.exp (D/2))^2 = Real.exp D := by
    rw [pow_two,←Real.exp_add]; congr 1; ring
  simpa only [one_mul,Real.cosh_add_sinh,ee,radialTransport_half_angle] using limit

/-- Even for one fixed displacement budget the exponential transport
factor is optimal. Its supremum is approached along the vertical rays. -/
theorem sharp_fixed_displacement_factor {D : ℝ} (hD : 0≤D) (C : ℝ) :
    (∀ z w Z W : ℍ, dist z Z+dist w W≤D → 1+pairU z w≤C*(1+pairU Z W)) ↔ Real.exp D≤C := by
  constructor
  · intro h
    apply le_of_tendsto (radial_transport_limit D)
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with r hr
    obtain ⟨z,w,Z,W,_,travel,attain⟩ := radial_transport_attained hr hD
    have hc := h z w Z W travel.le
    rw [attain] at hc
    exact le_of_mul_le_mul_right hc (by linarith only [pairU_nonneg Z W])
  · intro h z w Z W travel
    exact (one_add_pairU_transport z w Z W).trans (mul_le_mul_of_nonneg_right
      ((Real.exp_le_exp.mpr travel).trans h) (by linarith only [pairU_nonneg Z W]))


end GaloisForLFunctions.CompactHyperbolicSurfaces
