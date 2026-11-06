import GaloisForLFunctions.ThetaCuspSections.FiniteRankCriticalCollar

/-!
# A quantitative critical collar for every finite theta rank

A compact interval of positive boundary current supplies a factorial coercivity
bound through the integral Hilbert matrix. Cauchy estimates control aperture
perturbations of all moments by one factorial majorant. Their comparison gives
a rank-dependent collar with constants independent of rank.
-/

set_option autoImplicit false

noncomputable section
open Complex MeasureTheory Matrix Filter Topology Set
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ThetaCuspSections.QuantitativeCollar
open _root_.RHTower
open GaloisForLFunctions.ThetaCuspSections.CriticalCollar

/-- The moment matrix of uniform measure on the unit interval. -/
def unitMomentMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => 1 / ((i.val+j.val:ℕ)+1:ℝ)

private theorem unitMomentMatrix_posDef (N : ℕ) : (unitMomentMatrix N).PosDef := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  have hs (k : ℕ) : 1/((k:ℝ)+1) = ∫ x : ℝ, x^k ∂μ := by
    change _ = ∫ x : ℝ in Ioc (0:ℝ) 1, x^k
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_pow]
    norm_num
  have hi (k : ℕ) : Integrable (fun x : ℝ => x^k) μ :=
    (continuous_pow k).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hμ (F : Finset ℝ) : 0 < μ {x : ℝ | x∉F} := by
    have hF : μ (F : Set ℝ)=0 := F.finite_toSet.measure_zero μ
    have hu : μ Set.univ=1 := by simp [μ]
    change 0 < μ (F : Set ℝ)ᶜ
    rw [measure_compl F.measurableSet (by rw [hF]; exact ENNReal.zero_ne_top),hu,hF]
    simp
  have he : unitMomentMatrix N =
      HTGeometry.momentHankelMatrix (fun k : ℕ => 1/((k:ℝ)+1)) N := by
    ext i j
    rfl
  rw [he]
  exact HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (fun k : ℕ => 1/((k:ℝ)+1)) hs hi hμ N

/-- Clearing every moment denominator turns positivity into an integral determinant floor. -/
private theorem unitMomentMatrix_det_floor (N : ℕ) :
    1 / ((Nat.factorial (2*N):ℝ)^N) ≤ (unitMomentMatrix N).det := by
  let D : ℕ := Nat.factorial (2*N)
  let Z : Matrix (Fin N) (Fin N) ℤ := fun i j => (D/(i.val+j.val+1):ℕ)
  have hD : 0 < (D:ℝ) := by exact_mod_cast Nat.factorial_pos (2*N)
  have hscale : (Int.castRingHom ℝ).mapMatrix Z = (D:ℝ) • unitMomentMatrix N := by
    ext i j
    have hd : i.val+j.val+1 ∣ D := Nat.dvd_factorial (by omega) (by omega)
    have he : ((D/(i.val+j.val+1):ℕ):ℝ) * ((i.val+j.val+1:ℕ):ℝ) = (D:ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hd
    change ((D/(i.val+j.val+1):ℕ):ℝ) = (D:ℝ)*(1/((i.val+j.val:ℕ)+1:ℝ))
    rw [mul_one_div]
    apply (eq_div_iff (by positivity)).mpr
    simpa only [Nat.cast_add,Nat.cast_one] using he
  have hdet : (Z.det:ℝ) = (D:ℝ)^N*(unitMomentMatrix N).det := by
    change (Int.castRingHom ℝ) Z.det = _
    rw [(Int.castRingHom ℝ).map_det,hscale,Matrix.det_smul]
    simp only [Fintype.card_fin]
  have hZ : 0 < Z.det := by
    have hr : 0 < (Z.det:ℝ) := by
      rw [hdet]
      exact mul_pos (pow_pos hD N) (unitMomentMatrix_posDef N).det_pos
    exact_mod_cast hr
  have hZ1 : (1:ℝ) ≤ (Z.det:ℝ) := by exact_mod_cast (show (1:ℤ)≤Z.det by omega)
  change 1/(D:ℝ)^N ≤ _
  apply (div_le_iff₀ (pow_pos hD N)).mpr
  simpa only [hdet,mul_comm] using hZ1

/-- The determinant expansion bounds a cofactor by the number of its permutations. -/
private theorem abs_adjugate_le_factorial {n : ℕ}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hA : ∀ i j, |A i j|≤1)
    (i j : Fin (n+1)) : |A.adjugate i j| ≤ (Nat.factorial n:ℝ) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,abs_mul,abs_pow,abs_neg,abs_one,
    one_pow,one_mul]
  have h := Matrix.det_le (abv:=AbsoluteValue.abs) (A:=A.submatrix j.succAbove i.succAbove)
    (x:=1) (fun k l => hA _ _)
  simp only [Fintype.card_fin,one_pow,nsmul_eq_mul,mul_one] at h
  change |(A.submatrix j.succAbove i.succAbove).det| ≤ (Nat.factorial n:ℝ) at h
  exact h

private theorem unitMomentMatrix_inv_entry_bound (n : ℕ) (i j : Fin (n+1)) :
    |(unitMomentMatrix (n+1))⁻¹ i j| ≤
      (Nat.factorial n:ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1) := by
  have hd := (unitMomentMatrix_posDef (n+1)).det_pos
  have he (k l : Fin (n+1)) : |unitMomentMatrix (n+1) k l|≤1 := by
    unfold unitMomentMatrix
    rw [abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hadj := abs_adjugate_le_factorial he i j
  have hfloor := unitMomentMatrix_det_floor (n+1)
  have hD : 0 < (Nat.factorial (2*(n+1)):ℝ)^(n+1) := by positivity
  have hinv : ((unitMomentMatrix (n+1)).det)⁻¹ ≤
      (Nat.factorial (2*(n+1)):ℝ)^(n+1) := by
    have h := (inv_le_inv₀ hd (one_div_pos.mpr hD)).mpr hfloor
    simpa only [one_div,inv_inv] using h
  rw [Matrix.inv_def,Ring.inverse_eq_inv]
  change |((unitMomentMatrix (n+1)).det)⁻¹*(unitMomentMatrix (n+1)).adjugate i j|≤_
  rw [abs_mul,abs_inv,abs_of_pos hd]
  calc _ ≤ ((Nat.factorial (2*(n+1)):ℝ)^(n+1))*(Nat.factorial n:ℝ) :=
      mul_le_mul hinv hadj (abs_nonneg _) hD.le
    _ = _ := mul_comm _ _

/-- Completing a square turns an upper inverse-form bound into coercivity. -/
private theorem coercive_of_inverse_quadratic {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {B : ℝ} (hB : 0<B)
    (hbound : ∀ v : Fin N → ℝ, v ⬝ᵥ A⁻¹*ᵥv ≤ B*(v ⬝ᵥ v))
    (v : Fin N → ℝ) : v ⬝ᵥ v ≤ B*(v ⬝ᵥ A*ᵥv) := by
  have hentry (i j : Fin N) : A j i=A i j := by
    have h := congrFun (congrFun hA.isHermitian i) j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  have hsym (u w : Fin N → ℝ) : u ⬝ᵥ A*ᵥw=w ⬝ᵥ A*ᵥu := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hentry]
    ring
  have hcancel (w : Fin N → ℝ) : A*ᵥ(A⁻¹*ᵥw)=w := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.one_mulVec]
  have hquad : (B • v-A⁻¹*ᵥv) ⬝ᵥ A*ᵥ(B • v-A⁻¹*ᵥv) =
      B^2*(v ⬝ᵥ A*ᵥv)-2*B*(v ⬝ᵥ v)+(v ⬝ᵥ A⁻¹*ᵥv) := by
    simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,hcancel,sub_dotProduct,dotProduct_sub,
      smul_dotProduct,dotProduct_smul,smul_eq_mul]
    rw [hsym (A⁻¹*ᵥv) v,hcancel,dotProduct_comm (A⁻¹*ᵥv) v]
    ring
  have hy := hA.posSemidef.dotProduct_mulVec_nonneg (B • v-A⁻¹*ᵥv)
  rw [star_trivial,hquad] at hy
  have hb := hbound v
  have hz : 0 ≤ B*(B*(v ⬝ᵥ A*ᵥv)-(v ⬝ᵥ v)) := by nlinarith only [hy,hb]
  have h := (mul_nonneg_iff_of_pos_left hB).mp hz
  linarith only [h]

/-- The integer determinant floor and cofactor bound give a factorial coercivity constant. -/
theorem unitMomentMatrix_coercive (n : ℕ) (v : Fin (n+1) → ℝ) :
    v ⬝ᵥ v ≤ (Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1)*
      (v ⬝ᵥ unitMomentMatrix (n+1)*ᵥv) := by
  apply coercive_of_inverse_quadratic (unitMomentMatrix_posDef (n+1)) (by positivity)
  intro w
  have h := GaloisForLFunctions.HTGeometry.abs_dotProduct_mulVec_le
    (unitMomentMatrix (n+1))⁻¹ (by positivity) (unitMomentMatrix_inv_entry_bound n) w
  calc w ⬝ᵥ (unitMomentMatrix (n+1))⁻¹*ᵥw ≤
      |w ⬝ᵥ (unitMomentMatrix (n+1))⁻¹*ᵥw| := le_abs_self _
    _ ≤ (n+1:ℕ)*( (Nat.factorial n:ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1))*(w ⬝ᵥ w) := h
    _ = _ := by rw [Nat.factorial_succ]; push_cast; ring


/-- Cauchy circles inside a fixed strip give a uniform aperture Lipschitz bound. -/
private theorem horizontal_lipschitz {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (hbound : ∀ t a : ℝ, |a|≤3/4 →
      ‖f ((t:ℂ)+(a:ℂ)*I)‖≤C*Real.exp (-(δ*|t|)))
    (b a : ℝ) (ha : |a-1/2|≤1/8) :
    ‖f ((b:ℂ)-(a:ℂ)*I)-f ((b:ℂ)-((1/2:ℝ):ℂ)*I)‖ ≤
      8*C*Real.exp (δ/4)*Real.exp (-(δ*|b|))*|a-1/2| := by
  let z : ℂ := (b:ℂ)-((1/2:ℝ):ℂ)*I
  let y : ℂ := (b:ℂ)-(a:ℂ)*I
  let B : ℝ := C*Real.exp (δ/4)*Real.exp (-(δ*|b|))
  have hlarge (u : ℂ) (hu : ‖u-z‖≤1/4) : ‖f u‖≤B := by
    have him : |u.im|≤3/4 := by
      have hi := (Complex.abs_im_le_norm (u-z)).trans hu
      have hi' : |u.im+1/2|≤1/4 := by simpa [z] using hi
      have habs : |u.im| ≤ |u.im+1/2|+1/2 := by
        calc |u.im|=|(u.im+1/2)+(-1/2)| := by congr 1; ring
          _≤|u.im+1/2|+|-1/2| := abs_add_le _ _
          _=|u.im+1/2|+1/2 := by norm_num
      linarith only [hi',habs]
    have hre : |b|-1/4 ≤ |u.re| := by
      have hr := (Complex.abs_re_le_norm (u-z)).trans hu
      have hr' : |u.re-b|≤1/4 := by simpa [z] using hr
      have habs := abs_sub_abs_le_abs_sub b u.re
      rw [abs_sub_comm b u.re] at habs
      linarith only [hr',habs]
    have hfu := hbound u.re u.im him
    rw [Complex.re_add_im] at hfu
    have hexp : -(δ*|u.re|)≤δ/4+-(δ*|b|) := by
      have h := mul_le_mul_of_nonneg_left hre hδ
      nlinarith only [h]
    calc ‖f u‖ ≤ C*Real.exp (-(δ*|u.re|)) := hfu
      _ ≤ C*Real.exp (δ/4+-(δ*|b|)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = B := by rw [Real.exp_add]; dsimp [B]; ring
  have hder (w : ℂ) (hw : w∈Metric.closedBall z (1/8)) : ‖deriv f w‖≤8*B := by
    have hw' : ‖w-z‖≤1/8 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have hsphere (u : ℂ) (hu : u∈Metric.sphere w (1/8)) : ‖f u‖≤B := by
      apply hlarge
      have hu' : ‖u-w‖=1/8 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hu
      have h : ‖u-z‖≤‖u-w‖+‖w-z‖ := by
        rw [show u-z=(u-w)+(w-z) by ring]
        exact norm_add_le _ _
      rw [hu'] at h
      linarith only [h,hw']
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0:ℝ)<1/8) hf.diffContOnCl hsphere
    convert h using 1; ring
  have hdist : ‖y-z‖=|a-1/2| := by
    have he : y-z=(((1/2-a:ℝ):ℂ))*I := by dsimp [y,z]; push_cast; ring
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  have hz : z∈Metric.closedBall z (1/8) := by simp
  have hy : y∈Metric.closedBall z (1/8) := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,hdist] using ha
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w _ => hf w) hder (convex_closedBall z (1/8)) hz hy
  rw [hdist] at h
  change ‖f y-f z‖≤_
  calc ‖f y-f z‖ ≤ 8*B*|a-1/2| := h
    _ = _ := by dsimp [B]; ring


theorem current_difference_le (u₀ u v₀ v : ℂ) :
    |2*((starRingEnd ℂ) u*(-I*v)).re-2*((starRingEnd ℂ) u₀*(-I*v₀)).re| ≤
      2*(‖u-u₀‖*‖v‖+‖u₀‖*‖v-v₀‖) := by
  rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),← Complex.sub_re]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (Complex.abs_re_le_norm _).trans ?_
  have he : (starRingEnd ℂ) u*(-I*v)-(starRingEnd ℂ) u₀*(-I*v₀) =
      (starRingEnd ℂ) (u-u₀)*(-I*v)+(starRingEnd ℂ) u₀*(-I*(v-v₀)) := by
    rw [map_sub]
    ring
  rw [he]
  refine (norm_add_le _ _).trans_eq ?_
  simp only [norm_mul,Complex.norm_conj,norm_neg,Complex.norm_I,one_mul]

/-- Xi and its derivative retain exponential decay under aperture differences. -/
theorem current_lipschitz_exp : ∃ C : ℝ, 0<C ∧
    ∀ a : ℝ, |a-1/2|≤1/8 → ∀ b : ℝ,
      |current a b-current (1/2) b| ≤ C*|a-1/2| *Real.exp (-((Real.pi/4)*|b|)) := by
  let δ : ℝ := Real.pi/8
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hδpi : 2*δ<Real.pi/2 := by dsimp [δ]; linarith only [Real.pi_pos]
  obtain ⟨C₀,hC₀,h₀⟩ := RHTower.exists_norm_XiC_horizontal_le
    (A:=3/4) (δ:=δ) (by norm_num) hδ hδpi
  obtain ⟨C₁,hC₁,h₁⟩ := RHTower.exists_norm_XiC_deriv_horizontal_le
    (A:=3/4) (δ:=δ) (by norm_num) hδ hδpi
  have hd : Differentiable ℂ (deriv RHTower.XiC) := fun z =>
    ((RHTower.XiC_differentiable.analyticAt z).deriv).differentiableAt
  refine ⟨32*C₀*C₁*Real.exp (δ/4)+1,by positivity,fun a ha b => ?_⟩
  have haabs : |a|≤3/4 := by
    rcases abs_le.mp ha with ⟨hl,hu⟩
    exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩
  let z : ℂ := (b:ℂ)-(a:ℂ)*I
  let z₀ : ℂ := (b:ℂ)-((1/2:ℝ):ℂ)*I
  have hv : ‖deriv RHTower.XiC z‖≤C₁*Real.exp (-(δ*|b|)) := by
    simpa only [z,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      h₁ b (-a) (by simpa only [abs_neg] using haabs)
  have hu₀ : ‖RHTower.XiC z₀‖≤C₀*Real.exp (-(δ*|b|)) := by
    simpa only [z₀,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      h₀ b (-(1/2)) (by norm_num)
  have hdu := horizontal_lipschitz RHTower.XiC_differentiable hC₀ hδ h₀ b a ha
  have hdv := horizontal_lipschitz hd hC₁ hδ h₁ b a ha
  have hp₀ := mul_le_mul hdu hv (norm_nonneg _) (by positivity)
  have hp₁ := mul_le_mul hu₀ hdv (norm_nonneg _) (by positivity)
  have hdiff := current_difference_le (RHTower.XiC z₀) (RHTower.XiC z)
    (deriv RHTower.XiC z₀) (deriv RHTower.XiC z)
  change |current a b-current (1/2) b|≤_ at hdiff
  calc |current a b-current (1/2) b| ≤
      2*(‖RHTower.XiC z-RHTower.XiC z₀‖*‖deriv RHTower.XiC z‖+
        ‖RHTower.XiC z₀‖*‖deriv RHTower.XiC z-deriv RHTower.XiC z₀‖) := hdiff
    _ ≤ 2*((8*C₀*Real.exp (δ/4)*Real.exp (-(δ*|b|))*|a-1/2|)*
          (C₁*Real.exp (-(δ*|b|)))+
        (C₀*Real.exp (-(δ*|b|)))*
          (8*C₁*Real.exp (δ/4)*Real.exp (-(δ*|b|))*|a-1/2|)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp₀ hp₁) (by norm_num)
    _ = (32*C₀*C₁*Real.exp (δ/4))*|a-1/2| *Real.exp (-((Real.pi/4)*|b|)) := by
      rw [show -((Real.pi/4)*|b|)=-(δ*|b|)+-(δ*|b|) by dsimp [δ]; ring,
        Real.exp_add]
      ring
    _ ≤ _ := by gcongr; linarith


/-- Absorbing powers into exponential decay controls all moment orders with fixed constants. -/
private theorem rawMoment_lipschitz_factorial : ∃ M K : ℝ, 0<M ∧ 1≤ K ∧
    ∀ a : ℝ, |a-1/2|≤1/8 → ∀ n : ℕ,
      |rawMoment a n-rawMoment (1/2) n| ≤ M*K^n*(n.factorial:ℝ)*|a-1/2| := by
  obtain ⟨C,hC,hcurr⟩ := current_lipschitz_exp
  let E : ℝ→ℝ := fun b => Real.exp (-((Real.pi/8)*|b|))
  have hE : Integrable E :=
    integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by positivity)
  let I₀ : ℝ := ∫ b : ℝ, E b
  have hI₀ : 0≤I₀ := integral_nonneg fun b => (Real.exp_pos _).le
  let M : ℝ := C*(I₀+1)
  let K : ℝ := max 1 (8/Real.pi)
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨M,K,hM,le_max_left _ _,fun a ha n => ?_⟩
  have ha1 : |a|<1 := by
    rcases abs_le.mp ha with ⟨hl,hu⟩
    exact abs_lt.mpr ⟨by linarith only [hl],by linarith only [hu]⟩
  have hi : Integrable (fun b : ℝ => b^n*(current a b-current (1/2) b)) := by
    convert (raw_integrable a ha1 n).sub (raw_integrable (1/2) (by norm_num) n) using 1
    funext b
    simp only [Pi.sub_apply,mul_sub]
  let B : ℝ := C*|a-1/2| *(8/Real.pi)^n*(n.factorial:ℝ)
  have hmajor (b : ℝ) : |b^n*(current a b-current (1/2) b)|≤B*E b := by
    rw [abs_mul,abs_pow]
    have h := mul_le_mul_of_nonneg_left (hcurr a ha b) (pow_nonneg (abs_nonneg b) n)
    have hpow := pow_abs_mul_exp_neg_le (by positivity : (0:ℝ)<Real.pi/4) n b
    have h₂ := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤C*|a-1/2|)
    calc |b|^n*|current a b-current (1/2) b| ≤
        |b|^n*(C*|a-1/2| *Real.exp (-((Real.pi/4)*|b|))) := h
      _ = (C*|a-1/2|)*(|b|^n*Real.exp (-((Real.pi/4)*|b|))) := by ring
      _ ≤ (C*|a-1/2|)*((2/(Real.pi/4))^n*(n.factorial:ℝ)*
          Real.exp (-(((Real.pi/4)/2)*|b|))) := h₂
      _ = B*E b := by
        dsimp [B,E]
        rw [show (2:ℝ)/(Real.pi/4)=8/Real.pi by ring,
          show (Real.pi/4)/2=Real.pi/8 by ring]
        ring
  have hnorm : Integrable (fun b : ℝ => |b^n*(current a b-current (1/2) b)|) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hle := integral_mono hnorm (hE.const_mul B) hmajor
  rw [integral_const_mul] at hle
  have hCI : C*I₀≤M := by dsimp [M]; nlinarith only [hC]
  have hpow : (8/Real.pi)^n≤ K^n :=
    pow_le_pow_left₀ (by positivity) (le_max_right _ _) n
  have hcoeff : C*I₀*(8/Real.pi)^n≤M*K^n :=
    mul_le_mul hCI hpow (by positivity) hM.le
  have he : rawMoment a n-rawMoment (1/2) n =
      ∫ b : ℝ, b^n*(current a b-current (1/2) b) := by
    rw [rawMoment,rawMoment,← integral_sub (raw_integrable a ha1 n)
      (raw_integrable (1/2) (by norm_num) n)]
    congr 1
    funext b
    ring
  rw [he]
  calc |∫ b : ℝ, b^n*(current a b-current (1/2) b)| ≤
      ∫ b : ℝ, |b^n*(current a b-current (1/2) b)| := abs_integral_le_integral_abs
    _ ≤ B*I₀ := hle
    _ = (C*I₀*(8/Real.pi)^n)*(n.factorial:ℝ)*|a-1/2| := by dsimp [B]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (abs_nonneg _)


open Filter Topology _root_.RHTower
open GaloisForLFunctions.ThetaCuspSections.CriticalCollar

/-- Uniform moments on a compact interval supporting a positive current floor. -/
def compactMomentMatrix (r : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => r^(i.val+j.val+1)/((i.val+j.val:ℕ)+1:ℝ)

/-- The compact moment quadratic form is a polynomial-square integral. -/
theorem compactMomentMatrix_quad (r : ℝ) (hr : 0 < r) (N : ℕ) (v : Fin N → ℝ) :
    v ⬝ᵥ compactMomentMatrix r N*ᵥv =
      ∫ b : ℝ in Ioc 0 r, ((Polynomial.ofFn N v).eval b)^2 := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 r)
  have hs (k : ℕ) : r^(k+1)/((k:ℝ)+1) = ∫ b : ℝ, b^k ∂μ := by
    change _ = ∫ b : ℝ in Ioc 0 r, b^k
    rw [← intervalIntegral.integral_of_le hr.le,integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero k),sub_zero]
  have hi (k : ℕ) : Integrable (fun b : ℝ => b^k) μ :=
    (continuous_pow k).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  change v ⬝ᵥ HTGeometry.momentHankelMatrix (fun k => r^(k+1)/((k:ℝ)+1)) N*ᵥv = _
  rw [HTGeometry.dotProduct_mulVec_momentHankelMatrix,
    HTGeometry.momentFunctional_pow_two_eq_integral_sq _ hs hi]

/-- Rescaling a uniform interval is a scalar times a diagonal congruence. -/
theorem compactMomentMatrix_scale (r : ℝ) (N : ℕ) (v : Fin N → ℝ) :
    v ⬝ᵥ compactMomentMatrix r N*ᵥv =
      r*((fun i : Fin N => r^i.val*v i) ⬝ᵥ unitMomentMatrix N*ᵥ
        (fun i : Fin N => r^i.val*v i)) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,compactMomentMatrix,unitMomentMatrix,
    pow_add,pow_one]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Geometric diagonal rescaling loses at most `r^(2N)` in the coefficient norm. -/
theorem scaled_vector_floor {r : ℝ} (hr : 0 < r) (hr1 : r≤1)
    (N : ℕ) (v : Fin N → ℝ) :
    r^(2*N)*(v ⬝ᵥ v) ≤
      (fun i : Fin N => r^i.val*v i) ⬝ᵥ (fun i : Fin N => r^i.val*v i) := by
  rw [dotProduct,dotProduct,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp : r^(2*N)≤(r^i.val)^2 := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hr.le hr1 (by omega)
  have h := mul_le_mul_of_nonneg_right hp (sq_nonneg (v i))
  nlinarith only [h]

/-- The boundary current has a fixed positive lower bound on a compact frequency interval. -/
theorem current_boundary_floor : ∃ m r : ℝ, 0 < m ∧ 0 < r ∧ r≤1 ∧
    ∀ b : ℝ, b∈Icc 0 r → m≤ current (1/2) b := by
  let m : ℝ := current (1/2) 0/2
  have h0 := current_boundary_pos 0
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : ∀ᶠ b : ℝ in 𝓝 0, m < current (1/2) b :=
    (isOpen_lt continuous_const (current_continuous (1/2))).mem_nhds (by dsimp [m]; linarith only [h0])
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨m,min 1 (ε/2),hm,lt_min (by norm_num) (by positivity),min_le_left _ _,fun b hb => ?_⟩
  apply (hnear ?_).le
  have hsmall : b < ε := hb.2.trans_lt ((min_le_right _ _).trans_lt (by linarith only [hε]))
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hb.1] using hsmall

private theorem current_boundary_compact_comparison {m r : ℝ} (_hm : 0 < m) (hr : 0 < r)
    (hfloor : ∀ b : ℝ, b∈Icc 0 r → m≤ current (1/2) b)
    (N : ℕ) (v : Fin N → ℝ) :
    m*(v ⬝ᵥ compactMomentMatrix r N*ᵥv) ≤ v ⬝ᵥ rawHankel (1/2) N*ᵥv := by
  let p := Polynomial.ofFn N v
  have hraw : v ⬝ᵥ rawHankel (1/2) N*ᵥv = ∫ b : ℝ, (p.eval b)^2*current (1/2) b := by
    change v ⬝ᵥ HTGeometry.momentHankelMatrix (weightedMoment volume (current (1/2))) N*ᵥv = _
    rw [HTGeometry.dotProduct_mulVec_momentHankelMatrix,
      momentFunctional_rawMoment_eq_integral (raw_integrable (1/2) (by norm_num))]
    simp only [Polynomial.eval_pow,p]
  have hint : Integrable (fun b : ℝ => (p.eval b)^2*current (1/2) b) := by
    have h := integrable_polynomial_mul_of_rawMoments (raw_integrable (1/2) (by norm_num)) (p^2)
    convert h using 1
    funext b
    rw [Polynomial.eval_pow]
  have hsq : IntegrableOn (fun b : ℝ => (p.eval b)^2) (Ioc 0 r) :=
    (p.continuous.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcmp : (∫ b : ℝ in Ioc 0 r, m*(p.eval b)^2) ≤
      ∫ b : ℝ in Ioc 0 r, (p.eval b)^2*current (1/2) b := by
    apply integral_mono_ae (hsq.const_mul m) hint.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hfloor b ⟨hb.1.le,hb.2⟩) (sq_nonneg (p.eval b))
  have hwhole : (∫ b : ℝ in Ioc 0 r, (p.eval b)^2*current (1/2) b) ≤
      ∫ b : ℝ, (p.eval b)^2*current (1/2) b := by
    have hc : 0≤∫ b : ℝ in (Ioc 0 r)ᶜ, (p.eval b)^2*current (1/2) b :=
      integral_nonneg fun b => mul_nonneg (sq_nonneg _) (current_boundary_pos b).le
    have he := integral_add_compl (s:=Ioc (0:ℝ) r) measurableSet_Ioc hint
    linarith only [he,hc]
  rw [compactMomentMatrix_quad r hr,hraw,← integral_const_mul]
  exact hcmp.trans hwhole

/-- A compact positive current floor gives coercivity of every actual boundary moment matrix. -/
private theorem raw_boundary_factorial_floor : ∃ m r : ℝ, 0 < m ∧ 0 < r ∧ r≤1 ∧
    ∀ n : ℕ, ∀ v : Fin (n+1) → ℝ,
      m*r^(2*(n+1)+1)*(v ⬝ᵥ v) ≤
        ((Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1))*
          (v ⬝ᵥ rawHankel (1/2) (n+1)*ᵥv) := by
  obtain ⟨m,r,hm,hr,hr1,hfloor⟩ := current_boundary_floor
  refine ⟨m,r,hm,hr,hr1,fun n v => ?_⟩
  let w : Fin (n+1) → ℝ := fun i => r^i.val*v i
  let B : ℝ := (Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1)
  have hB : 0≤B := by dsimp [B]; positivity
  have hnorm := scaled_vector_floor hr hr1 (n+1) v
  have hunit := unitMomentMatrix_coercive n w
  have hcmp := current_boundary_compact_comparison hm hr hfloor (n+1) v
  calc m*r^(2*(n+1)+1)*(v ⬝ᵥ v) = (m*r)*(r^(2*(n+1))*(v ⬝ᵥ v)) := by rw [pow_succ]; ring
    _ ≤ (m*r)*(w ⬝ᵥ w) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ (m*r)*(B*(w ⬝ᵥ unitMomentMatrix (n+1)*ᵥw)) :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = B*(m*(v ⬝ᵥ compactMomentMatrix r (n+1)*ᵥv)) := by
      rw [compactMomentMatrix_scale]
      dsimp [w]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcmp hB


private theorem factorial_ratio_bound (N : ℕ) :
    (N:ℝ)*(N.factorial:ℝ)*(Nat.factorial (2*N):ℝ)^(N+1) ≤
      (Nat.factorial (2*N+1):ℝ)^(N+2) := by
  have hnat : N*N.factorial ≤ Nat.factorial (2*N+1) := by
    calc N*N.factorial ≤ (2*N+1)*Nat.factorial (2*N) :=
        Nat.mul_le_mul (by omega) (Nat.factorial_le (by omega))
      _ = Nat.factorial (2*N+1) := by rw [Nat.factorial_succ]
  have hfirst : (N:ℝ)*(N.factorial:ℝ) ≤ (Nat.factorial (2*N+1):ℝ) := by exact_mod_cast hnat
  have hfac : (Nat.factorial (2*N):ℝ) ≤ (Nat.factorial (2*N+1):ℝ) := by
    exact_mod_cast Nat.factorial_le (show 2*N≤2*N+1 by omega)
  calc (N:ℝ)*(N.factorial:ℝ)*(Nat.factorial (2*N):ℝ)^(N+1) ≤
      (Nat.factorial (2*N+1):ℝ)*(Nat.factorial (2*N+1):ℝ)^(N+1) :=
        mul_le_mul hfirst (pow_le_pow_left₀ (by positivity) hfac (N+1)) (by positivity) (by positivity)
    _ = _ := by rw [show N+2=(N+1)+1 by omega,pow_succ]; ring

private theorem aperture_power_bound {A K r : ℝ} (hA : 1≤A) (hr : 0 < r)
    (hK : K^2≤A*r^2) (N : ℕ) : K^(2*N)≤A^(N+1)*r^(2*N) := by
  have h := pow_le_pow_left₀ (sq_nonneg K) hK N
  simp only [mul_pow,← pow_mul] at h
  have hA0 : 0≤A := zero_le_one.trans hA
  have hp : A^N≤A^(N+1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hA0 N) hA
  exact h.trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hr.le _))

/-- The factorial denominator pays for both inverse coercivity and the moment perturbation. -/
private theorem aperture_radius_factor_bound {A K r M c : ℝ}
    (hA : 1≤A) (hr : 0 < r) (hM : 0 < M) (hc : 0 < c) (hK : K^2≤A*r^2) (N : ℕ) :
    ((N:ℝ)*M*K^(2*N)*(Nat.factorial (2*N):ℝ)*
      ((N.factorial:ℝ)*(Nat.factorial (2*N):ℝ)^N))*
        (c/(A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2))) ≤ M*c*r^(2*N) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hp := aperture_power_bound hA hr hK N
  have hf := factorial_ratio_bound N
  have hprod := mul_le_mul hp hf (by positivity : 0≤(N:ℝ)*(N.factorial:ℝ)*
    (Nat.factorial (2*N):ℝ)^(N+1)) (by positivity : 0≤A^(N+1)*r^(2*N))
  have h := mul_le_mul_of_nonneg_left hprod (mul_pos hM hc).le
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2))).mpr
  convert h using 1 <;> simp only [pow_succ] <;> ring


private theorem raw_entry_perturbation {M K : ℝ} (hM : 0 < M) (hK : 1≤ K)
    (hmom : ∀ a : ℝ, |a-1/2|≤1/8 → ∀ k : ℕ,
      |rawMoment a k-rawMoment (1/2) k|≤M*K^k*(k.factorial:ℝ)*|a-1/2|)
    (N : ℕ) (a : ℝ) (ha : |a-1/2|≤1/8) (i j : Fin N) :
    |(rawHankel a N-rawHankel (1/2) N) i j| ≤
      M*K^(2*N)*(Nat.factorial (2*N):ℝ)*|a-1/2| := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hij : i.val+j.val≤2*N := by omega
  have hp := pow_le_pow_right₀ hK hij
  have hf : (Nat.factorial (i.val+j.val):ℝ) ≤ (Nat.factorial (2*N):ℝ) := by
    exact_mod_cast Nat.factorial_le hij
  have hprod := mul_le_mul hp hf (by positivity) (by positivity)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod hM.le) (abs_nonneg (a-1/2))
  have h := (hmom a ha (i.val+j.val)).trans (by simpa only [mul_assoc] using hbound)
  simpa only [rawHankel, Matrix.sub_apply, mul_assoc] using h

/-- A single factorial law controls the critical collar at every finite rank. -/
theorem signedHankel_posDef_factorial_collar : ∃ A c : ℝ, 1≤A ∧ 0 < c ∧
    ∀ N : ℕ, ∀ a : ℝ,
      |a-1/2| < c/(A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2)) →
      (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  obtain ⟨M,K,hM,hK,hmom⟩ := rawMoment_lipschitz_factorial
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨m,r,hm,hr,hr1,hfloor⟩ := raw_boundary_factorial_floor
  let A : ℝ := 1+(K/r)^2
  have hA : 1≤A := by dsimp [A]; nlinarith only [sq_nonneg (K/r)]
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hKsq : K^2≤A*r^2 := by
    have he : A*r^2=r^2+K^2 := by dsimp [A]; field_simp [hr.ne']
    rw [he]
    exact le_add_of_nonneg_left (sq_nonneg r)
  let c : ℝ := min (1/8) (m*r/(2*M))
  have hc : 0 < c := lt_min (by norm_num) (div_pos (mul_pos hm hr) (by positivity))
  have hcsmall : c≤1/8 := min_le_left _ _
  have hMc : M*c ≤ m*r/2 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ) < 2*M)).mp (min_le_right (1/8) (m*r/(2*M)))
    change c*(2*M) ≤ m*r at h
    nlinarith only [h]
  have hradius (N : ℕ) : c/(A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2))≤ c := by
    have hfac : (1:ℝ)≤(Nat.factorial (2*N+1):ℝ) := by
      have hf : 1≤Nat.factorial (2*N+1) := by have h := Nat.factorial_pos (2*N+1); omega
      exact_mod_cast hf
    have hden : (1:ℝ)≤A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2) := by
      calc (1:ℝ) = 1*1 := by norm_num
        _ ≤ A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2) :=
          mul_le_mul (one_le_pow₀ hA) (one_le_pow₀ hfac) (by norm_num) (by positivity)
    apply (div_le_iff₀ (zero_lt_one.trans_le hden)).mpr
    exact le_mul_of_one_le_right hc.le hden
  refine ⟨A,c,hA,hc,fun N a ha => ?_⟩
  have hsmall : |a-1/2|≤1/8 := (ha.le.trans (hradius N)).trans hcsmall
  have ha1 : |a|<1 := by
    rcases abs_le.mp hsmall with ⟨hl,hu⟩
    exact abs_lt.mpr ⟨by linarith only [hl],by linarith only [hu]⟩
  apply signed_posDef_of_raw ha1 N
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a N,fun v hv => ?_⟩
  rw [star_trivial]
  cases N with
  | zero => exact False.elim (hv (Subsingleton.elim v 0))
  | succ n =>
    let B : ℝ := (Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1)
    let T : ℝ := (n+1:ℕ)*M*K^(2*(n+1))*(Nat.factorial (2*(n+1)):ℝ)
    let E : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := rawHankel a (n+1)-rawHankel (1/2) (n+1)
    have hB : 0 < B := by dsimp [B]; positivity
    have hT : 0≤T := by dsimp [T]; positivity
    have hpay : B*T*|a-1/2|≤ m*r^(2*(n+1)+1)/2 := by
      calc B*T*|a-1/2| = (T*B)*|a-1/2| := by ring
        _ ≤ (T*B)*(c/(A^((n+1)+1)*(Nat.factorial (2*(n+1)+1):ℝ)^((n+1)+2))) :=
          mul_le_mul_of_nonneg_left ha.le (mul_nonneg hT hB.le)
        _ ≤ M*c*r^(2*(n+1)) := aperture_radius_factor_bound hA hr hM hc hKsq (n+1)
        _ ≤ (m*r/2)*r^(2*(n+1)) := mul_le_mul_of_nonneg_right hMc (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have hentry := raw_entry_perturbation hM hK hmom (n+1) a hsmall
    have he := GaloisForLFunctions.HTGeometry.abs_dotProduct_mulVec_le E (by positivity) hentry v
    have he' : |v ⬝ᵥ E*ᵥv|≤(T*|a-1/2|)*(v ⬝ᵥ v) := by
      convert he using 1
      dsimp only [T]
      ring
    have hnorm : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (Ne.symm (fun h => hv ((dotProduct_self_eq_zero).mp h)))
    have hsplit : v ⬝ᵥ rawHankel a (n+1)*ᵥv =
        v ⬝ᵥ rawHankel (1/2) (n+1)*ᵥv+v ⬝ᵥ E*ᵥv := by
      have hmat : rawHankel a (n+1)=rawHankel (1/2) (n+1)+E := by dsimp [E]; abel
      rw [hmat,Matrix.add_mulVec,dotProduct_add]
    have hsplitB := congrArg (fun q : ℝ => B*q) hsplit
    have hlow := mul_le_mul_of_nonneg_left (abs_le.mp he').1 hB.le
    have hpaid := mul_le_mul_of_nonneg_right hpay hnorm.le
    have hzero := hfloor n v
    change m*r^(2*(n+1)+1)*(v ⬝ᵥ v)≤B*(v ⬝ᵥ rawHankel (1/2) (n+1)*ᵥv) at hzero
    have hfinal : (m*r^(2*(n+1)+1)/2)*(v ⬝ᵥ v)≤B*(v ⬝ᵥ rawHankel a (n+1)*ᵥv) := by
      nlinarith only [hzero,hlow,hpaid,hsplitB]
    have hpos : 0 < (m*r^(2*(n+1)+1)/2)*(v ⬝ᵥ v) := by positivity
    exact (mul_pos_iff_of_pos_left hB).mp (hpos.trans_le hfinal)

/-- The factorial collar for rank `N` works simultaneously for all smaller sections. -/
theorem signedHankel_posDef_factorial_collar_upto : ∃ A c : ℝ, 1≤A ∧ 0 < c ∧
    ∀ N : ℕ, ∀ n≤N, ∀ a : ℝ,
      |a-1/2| < c/(A^(N+1)*(Nat.factorial (2*N+1):ℝ)^(N+2)) →
      (thetaCuspCenterMixedSignedHankel a n).PosDef := by
  obtain ⟨A,c,hA,hc,hp⟩ := signedHankel_posDef_factorial_collar
  refine ⟨A,c,hA,hc,fun N n hn a ha => ?_⟩
  have hinj : Function.Injective (Fin.castLE hn) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) hij
  have he : (thetaCuspCenterMixedSignedHankel a N).submatrix (Fin.castLE hn) (Fin.castLE hn) =
      thetaCuspCenterMixedSignedHankel a n := by ext i j; rfl
  simpa only [he] using (hp N a ha).submatrix hinj


end GaloisForLFunctions.ThetaCuspSections.QuantitativeCollar
