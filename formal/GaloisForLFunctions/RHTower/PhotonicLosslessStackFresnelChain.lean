import GaloisForLFunctions.RHTower.PhotonicLosslessTemporalStackRealZeros
import GaloisForLFunctions.RHTower.ComplexFugacityChainFieldDensity
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap

/-!
# Lossless temporal stacks are Fresnel Lee–Yang chains, and Ξ excludes long slabs

In the right/left-moving wave basis `y ↦ (y₁ + y₂, iκ(y₁ - y₂))` of a medium of
impedance `κ`, a lossless temporal slab of duration `τ` is the diagonal phase
`diag(e^{ikτ}, e^{-ikτ})`. The change of basis across an impedance step `a → b`
is `((a + b)/2b) [[1, r], [r, 1]]` with the Fresnel coefficient
`r = (b - a)/(b + a)`, and `|r| < 1`. Hence the displacement entry of an
indexed lossless stack is, exactly,

  `A(k) = ½ e^{ik Σ τ_j} ∏ (κ_{j+1} + κ_j)/(2κ_{j+1}) · Z(k)`,

where `Z` is the complex-fugacity Lee–Yang chain partition function with wall
fugacities equal to the Fresnel coefficients and site fields `e^{-2ikτ_j}`.
Every lossless temporal Maxwell stack is therefore a ferromagnetic Lee–Yang
chain with frequencies `2τ_j`, and the Lee–Yang field-density budget applies.

Ξ has no zeros in the centered slab `|Re z| ≤ 13/2`. In the disc of diameter
`[-1/2, 13/2]` a normalized locally uniform approximant of Ξ therefore
eventually has no zeros. A slab of duration `τ > π/6` would force one there. So
every sequence of lossless temporal stacks converging, after any nonzero
normalization, to Ξ eventually has all slab durations at most `π/6`. In
particular no lossless prime-log stack, whose slab durations `log p ≥ log 2`
exceed `π/6`, can converge to Ξ. A temporal-photonic realization of Ξ must be a
thin-slab continuum, and the primes cannot enter as slab durations.
-/

open Complex Metric Set Filter Topology Finset
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Indexed lossless stack: slab `0` acts first and slab `N` acts last. -/
def ptrLosslessStackSeq (κ τ : ℕ → ℝ) : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, k => ptrLosslessSlab (κ 0) (τ 0) k
  | N + 1, k => ptrLosslessSlab (κ (N + 1)) (τ (N + 1)) k * ptrLosslessStackSeq κ τ N k

/-- Displacement/induction amplitudes of right- and left-moving waves in a medium of
impedance `κ`. -/
def ptrWave (κ : ℝ) (y : ℂ × ℂ) : Fin 2 → ℂ :=
  ![y.1 + y.2, Complex.I * κ * (y.1 - y.2)]

/-- Fresnel reflection coefficient of the impedance step `a → b`. -/
def ptrFresnel (a b : ℝ) : ℝ := (b - a) / (b + a)

/-- Fresnel transmission normalization of the impedance step `a → b`. -/
def ptrFresnelScale (a b : ℝ) : ℂ := ((b + a) / (2 * b) : ℝ)

theorem ptrWave_smul (κ : ℝ) (c : ℂ) (y : ℂ × ℂ) :
    ptrWave κ (c * y.1, c * y.2) = c • ptrWave κ y := by
  ext i; fin_cases i <;> simp [ptrWave] <;> ring

/-- A lossless slab is diagonal in its own wave basis. -/
theorem ptrLosslessSlab_mulVec_wave (κ τ : ℝ) (k : ℂ) (y : ℂ × ℂ) (hκ : κ ≠ 0) :
    (ptrLosslessSlab κ τ k).mulVec (ptrWave κ y) =
      ptrWave κ (Complex.exp (k * τ * Complex.I) * y.1,
        Complex.exp (-(k * τ * Complex.I)) * y.2) := by
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have e1 : Complex.exp (k * τ * Complex.I) = Complex.cos (k * τ) + Complex.sin (k * τ) * I :=
    Complex.exp_mul_I _
  have e2 : Complex.exp (-(k * τ * Complex.I)) =
      Complex.cos (k * τ) - Complex.sin (k * τ) * I := by
    rw [show -(k * τ * Complex.I) = (-(k * τ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  rw [e1, e2]
  ext i
  fin_cases i
  · simp only [ptrLosslessSlab, ptrWave, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    field_simp
    ring_nf
  · simp only [ptrLosslessSlab, ptrWave, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The wave basis of impedance `a` re-expressed in the wave basis of impedance `b`. -/
theorem ptrWave_fresnel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℂ × ℂ) :
    ptrWave a y = ptrFresnelScale a b •
      ptrWave b (y.1 + (ptrFresnel a b : ℂ) * y.2, (ptrFresnel a b : ℂ) * y.1 + y.2) := by
  have hab : (b + a : ℂ) ≠ 0 := by exact_mod_cast (by linarith : b + a ≠ 0)
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  ext i
  fin_cases i <;> simp [ptrWave, ptrFresnel, ptrFresnelScale] <;> field_simp <;> ring

theorem ptrFresnel_norm_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖((ptrFresnel a b : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, ptrFresnel, abs_div, abs_of_pos (by linarith : 0 < b + a),
    div_le_one (by linarith)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem ptrFresnelScale_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ptrFresnelScale a b ≠ 0 := by
  unfold ptrFresnelScale
  exact_mod_cast (by positivity : (b + a) / (2 * b) ≠ 0)

/-- Wall fugacities of the Fresnel chain. -/
def ptrFresnelWall (κ : ℕ → ℝ) (j : ℕ) : ℂ := (ptrFresnel (κ j) (κ (j + 1)) : ℂ)

/-- Site fields of the Fresnel chain. -/
def ptrFresnelField (τ : ℕ → ℝ) (k : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-(Complex.I * ((2 * τ j : ℝ) : ℂ) * k))

/-- Accumulated scalar prefactor of the Fresnel chain. -/
def ptrFresnelPrefactor (κ τ : ℕ → ℝ) (k : ℂ) (N : ℕ) : ℂ :=
  (1 / 2) * (∏ j ∈ range (N + 1), Complex.exp (k * τ j * Complex.I)) *
    ∏ j ∈ range N, ptrFresnelScale (κ j) (κ (j + 1))

/-- **Fresnel dictionary, vector form.** -/
theorem ptrLosslessStackSeq_mulVec_eq (κ τ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (k : ℂ) (N : ℕ) :
    (ptrLosslessStackSeq κ τ N k).mulVec ![1, 0] =
      ptrFresnelPrefactor κ τ k N •
        ptrWave (κ N) (LeeYangChain.cChainPair (ptrFresnelWall κ) (ptrFresnelField τ k) N) := by
  induction N with
  | zero =>
    have hw : (![1, 0] : Fin 2 → ℂ) = ptrWave (κ 0) (1 / 2, 1 / 2) := by
      ext i; fin_cases i <;> simp [ptrWave]; norm_num
    rw [ptrLosslessStackSeq, hw, ptrLosslessSlab_mulVec_wave _ _ _ _ (hκ 0).ne']
    have hsplit : Complex.exp (-(k * τ 0 * Complex.I)) =
        Complex.exp (k * τ 0 * Complex.I) * ptrFresnelField τ k 0 := by
      rw [ptrFresnelField, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hsplit]
    simp only [ptrFresnelPrefactor, LeeYangChain.cChainPair]
    rw [← ptrWave_smul]
    congr 1
    ext <;> simp <;> ring
  | succ N ih =>
    set w := LeeYangChain.cChainPair (ptrFresnelWall κ) (ptrFresnelField τ k) N with hwdef
    have hsplit : Complex.exp (-(k * τ (N + 1) * Complex.I)) =
        Complex.exp (k * τ (N + 1) * Complex.I) * ptrFresnelField τ k (N + 1) := by
      rw [ptrFresnelField, ← Complex.exp_add]
      congr 1; push_cast; ring
    have hpair : LeeYangChain.cChainPair (ptrFresnelWall κ) (ptrFresnelField τ k) (N + 1) =
        (w.1 + ptrFresnelWall κ N * w.2,
          ptrFresnelField τ k (N + 1) * (ptrFresnelWall κ N * w.1 + w.2)) := by
      simp only [LeeYangChain.cChainPair, hwdef, ptrFresnelWall, Complex.conj_ofReal]
    have hpref : ptrFresnelPrefactor κ τ k (N + 1) =
        ptrFresnelPrefactor κ τ k N * ptrFresnelScale (κ N) (κ (N + 1)) *
          Complex.exp (k * τ (N + 1) * Complex.I) := by
      simp only [ptrFresnelPrefactor, prod_range_succ]
      ring
    have hw : ∀ (E u y₁ y₂ : ℂ), ptrWave (κ (N + 1)) (E * y₁, E * u * y₂) =
        E • ptrWave (κ (N + 1)) (y₁, u * y₂) := by
      intro E u y₁ y₂
      rw [← ptrWave_smul, mul_assoc]
    rw [ptrLosslessStackSeq, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
      ptrWave_fresnel (hκ N) (hκ (N + 1)), Matrix.mulVec_smul,
      ptrLosslessSlab_mulVec_wave _ _ _ _ (hκ (N + 1)).ne', smul_smul, hsplit, hw, smul_smul,
      hpair, hpref]
    simp only [ptrFresnelWall]

/-- **Fresnel dictionary.** The displacement entry of a lossless stack is the
Fresnel Lee–Yang chain partition function times a zero-free scalar. -/
theorem ptrLosslessStackSeq_entry_eq (κ τ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (k : ℂ) (N : ℕ) :
    ptrLosslessStackSeq κ τ N k 0 0 =
      ptrFresnelPrefactor κ τ k N *
        LeeYangChain.cChainZ (ptrFresnelWall κ) (ptrFresnelField τ k) N := by
  have h := congrFun (ptrLosslessStackSeq_mulVec_eq κ τ hκ k N) 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero] at h
  rw [h, LeeYangChain.cChainZ]
  simp [ptrWave]

private theorem cChainPair_congr (α : ℕ → ℂ) {u u' : ℕ → ℂ} {N : ℕ}
    (h : ∀ k ≤ N, u k = u' k) : ∀ k ≤ N,
      LeeYangChain.cChainPair α u k = LeeYangChain.cChainPair α u' k := by
  intro k
  induction k with
  | zero => intro _; simp [LeeYangChain.cChainPair, h 0 (Nat.zero_le _)]
  | succ k ih =>
    intro hk
    simp only [LeeYangChain.cChainPair, ih (by omega), h (k + 1) hk]

/-- The Fresnel chain as a Lee–Yang restriction with frequencies `2τ_j`. -/
theorem ptrFresnelChain_eq_restr (κ τ : ℕ → ℝ) (k : ℂ) (N : ℕ) :
    LeeYangChain.cChainZ (ptrFresnelWall κ) (ptrFresnelField τ k) N =
      LeeYangChain.cChainRestr N (ptrFresnelWall κ) (fun j : Fin (N + 1) => 2 * τ j) k := by
  rw [LeeYangChain.cChainRestr, LeeYangChain.cChainZ, LeeYangChain.cChainZ]
  rw [cChainPair_congr _ (u' := LeeYangChain.chainExt N
      fun j : Fin (N + 1) => Complex.exp (-(Complex.I * ((2 * τ j : ℝ) : ℂ) * k)))
    (fun j hj => by simp [LeeYangChain.chainExt, show j < N + 1 by omega, ptrFresnelField]) N le_rfl]

/-- Multiplying by `exp (S z)` does not change the disc zero count. -/
theorem zeroSumBall_exp_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (S c : ℂ) {t : ℝ}
    (ht : 0 ≤ t) (hsph : ∀ z ∈ sphere c t, f z ≠ 0) :
    zeroSumBall (fun z => Complex.exp (S * z) * f z) c t = zeroSumBall f c t := by
  unfold zeroSumBall
  congr 1
  have hcongr : EqOn (fun z => logDeriv (fun z => Complex.exp (S * z) * f z) z)
      (fun z => S + logDeriv f z) (sphere c t) := by
    intro z hz
    show logDeriv (fun z => Complex.exp (S * z) * f z) z = S + logDeriv f z
    have hexp : DifferentiableAt ℂ (fun z => Complex.exp (S * z)) z :=
      (Complex.differentiable_exp.comp (differentiable_const S |>.mul differentiable_id)) z
    rw [logDeriv_mul (f := fun z => Complex.exp (S * z)) (g := f) z (Complex.exp_ne_zero _)
      (hsph z hz) hexp (hf z)]
    congr 1
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun z => Complex.exp (S * z)) (Complex.exp (S * z) * S) z := by
      simpa using ((hasDerivAt_id z).const_mul S).cexp
    rw [hd.deriv]
    field_simp [Complex.exp_ne_zero]
  rw [circleIntegral.integral_congr ht hcongr]
  have hlog : ContinuousOn (fun z => logDeriv f z) (sphere c t) := by
    intro z hz
    have hcont : ContinuousAt (deriv f) z :=
      ((hf.analyticAt z).deriv).continuousAt
    exact (hcont.div (hf z).continuousAt (hsph z hz)).continuousWithinAt
  rw [circleIntegral.integral_add (continuousOn_const.circleIntegrable ht)
    (hlog.circleIntegrable ht)]
  have hzero : (∮ z in C(c, t), S) = 0 := by
    have := circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := fun z => S * z)
      (f' := fun _ => S) (c := c) ht (fun z _ => by
        simpa using ((hasDerivAt_id z).const_mul S).hasDerivWithinAt)
    simpa using this
  rw [hzero, zero_add]

theorem ptrFresnelWall_norm_le {κ : ℕ → ℝ} (hκ : ∀ j, 0 < κ j) (j : ℕ) :
    ‖ptrFresnelWall κ j‖ ≤ 1 :=
  ptrFresnel_norm_le (hκ j) (hκ (j + 1))

/-- The prefactor is a nonzero constant times `exp (i Στ_j · k)`. -/
theorem ptrFresnelPrefactor_eq (κ τ : ℕ → ℝ) (k : ℂ) (N : ℕ) :
    ptrFresnelPrefactor κ τ k N =
      ((1 / 2) * ∏ j ∈ range N, ptrFresnelScale (κ j) (κ (j + 1))) *
        Complex.exp ((Complex.I * ∑ j ∈ range (N + 1), (τ j : ℂ)) * k) := by
  rw [ptrFresnelPrefactor, ← Complex.exp_sum]
  have : ∑ j ∈ range (N + 1), k * (τ j : ℂ) * Complex.I =
      (Complex.I * ∑ j ∈ range (N + 1), (τ j : ℂ)) * k := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  ring

/-- **Producer budget for lossless temporal stacks.** If normalized lossless
stack entries converge locally uniformly to `g`, with `g` zero-free on the circle
`|z - T/2| = T/2 + η`, then eventually the Lee–Yang budget of the slab
frequencies `2τ_j` is at most the zero count of `g` in that disc. -/
theorem ptrLosslessStackSeq_eventually_budget
    (κ τ : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (c : ℕ → ℂ)
    (hκ : ∀ n j, 0 < κ n j) (hτ : ∀ n j, 0 < τ n j) (hc : ∀ n, c n ≠ 0)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hconv : TendstoLocallyUniformly
      (fun n k => c n * ptrLosslessStackSeq (κ n) (τ n) (N n) k 0 0) g atTop)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), g z ≠ 0) :
    ∀ᶠ n in atTop, ∑ j : Fin (N n + 1),
      (((⌈(2 * τ n j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
        (zeroSumBall g ((T : ℂ) / 2) (T / 2 + η)).re := by
  let L : ∀ n, LeeYangCount.LeeYangDatum (Fin (N n + 1)) := fun n =>
    LeeYangChain.cChainDatum (N n) (ptrFresnelWall (κ n))
      (ptrFresnelWall_norm_le (hκ n)) (fun j => 2 * τ n j)
      (fun j => by have := hτ n j; positivity)
  have hrestr : ∀ n k, (L n).restr k =
      LeeYangChain.cChainZ (ptrFresnelWall (κ n)) (ptrFresnelField (τ n) k) (N n) := by
    intro n k
    rw [ptrFresnelChain_eq_restr]
    exact LeeYangChain.cChainDatum_restr _ _ _ _ _ k
  let K : ℕ → ℂ := fun n => c n * ((1 / 2) *
    ∏ j ∈ range (N n), ptrFresnelScale (κ n j) (κ n (j + 1)))
  let S : ℕ → ℂ := fun n => Complex.I * ∑ j ∈ range (N n + 1), (τ n j : ℂ)
  have hK : ∀ n, K n ≠ 0 := by
    intro n
    refine mul_ne_zero (hc n) (mul_ne_zero (by norm_num) ?_)
    exact Finset.prod_ne_zero_iff.mpr fun j _ => ptrFresnelScale_ne_zero (hκ n j) (hκ n (j + 1))
  have hF : ∀ n, (fun k => c n * ptrLosslessStackSeq (κ n) (τ n) (N n) k 0 0) =
      fun k => K n * (Complex.exp (S n * k) * (L n).restr k) := by
    intro n
    funext k
    rw [ptrLosslessStackSeq_entry_eq _ _ (hκ n), ptrFresnelPrefactor_eq, hrestr]
    ring
  have hdiff : ∀ n, Differentiable ℂ (fun k => c n * ptrLosslessStackSeq (κ n) (τ n) (N n) k 0 0) := by
    intro n
    rw [hF n]
    exact ((Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)).mul
      (L n).differentiable_restr).const_mul _
  have hH := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hdiff hg hconv
    (c := (T : ℂ) / 2) (r := T / 2 + η) (R := T / 2 + η + 1) (by positivity) (by linarith) hsph
  have hS := LeeYangCount.eventually_ne_zero_on_sphere hg.continuous hconv hsph
  filter_upwards [hH, hS] with n ha hs
  have hsph' : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), (L n).restr z ≠ 0 := by
    intro z hz h
    apply hs z hz
    have h2 : (fun k => K n * (Complex.exp (S n * k) * (L n).restr k)) z = 0 := by
      show K n * (Complex.exp (S n * z) * (L n).restr z) = 0
      rw [h, mul_zero, mul_zero]
    exact (congrFun (hF n) z).trans h2
  have hb := LeeYangCount.sum_ceil_sub_one_le_zeroSumBall (L n)
    (LeeYangChain.cChainDatum_degreeOf _ _ _ _ _) hT hη hsph'
  have hcount : zeroSumBall (fun k => c n * ptrLosslessStackSeq (κ n) (τ n) (N n) k 0 0)
      ((T : ℂ) / 2) (T / 2 + η) = zeroSumBall (L n).restr ((T : ℂ) / 2) (T / 2 + η) := by
    rw [hF n, LeeYangCount.zeroSumBall_const_mul (hK n),
      zeroSumBall_exp_mul (L n).differentiable_restr _ _ (by positivity) hsph']
  rw [← hcount, ha] at hb
  exact hb

/-- `Ξ` has no zero in the closed disc `|z - 3| ≤ 7/2`. -/
theorem XiC_ne_zero_of_mem_closedBall_three {z : ℂ} (hz : z ∈ closedBall (3 : ℂ) (7 / 2)) :
    XiC z ≠ 0 := by
  apply XiC_ne_zero_of_abs_re_le_thirteen_halves
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h := (Complex.abs_re_le_norm (z - 3)).trans hz
  simp only [Complex.sub_re] at h
  norm_num at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem zeroSumBall_XiC_three : zeroSumBall XiC ((6 : ℝ) / 2 : ℂ) (6 / 2 + 1 / 2) = 0 := by
  have hc : ((6 : ℝ) / 2 : ℂ) = 3 := by push_cast; norm_num
  have hr : (6 : ℝ) / 2 + 1 / 2 = 7 / 2 := by norm_num
  rw [hc, hr]
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (c := (3 : ℂ)) (t := 7 / 2)
    (R := 7 / 2 + 1) (U := univ) (by norm_num) (by norm_num) isOpen_univ (subset_univ _)
    hXiCd.differentiableOn (fun ζ hζ => XiC_ne_zero_of_mem_closedBall_three
      (sphere_subset_closedBall hζ))
  have hZ : Z = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro ρ hρ
    have hzero := (hZzero ρ (hZball ρ hρ)).mpr hρ
    exact XiC_ne_zero_of_mem_closedBall_three (ball_subset_closedBall (hZball ρ hρ)) hzero
  rw [hsum, hZ, Finset.sum_empty]

/-- **Ξ excludes long lossless slabs.** If normalized displacement entries of
lossless temporal stacks converge locally uniformly to `Ξ`, then eventually every
slab has duration at most `π/6`. -/
theorem ptrLosslessStackSeq_slab_le_of_tendsto_XiC
    (κ τ : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (c : ℕ → ℂ)
    (hκ : ∀ n j, 0 < κ n j) (hτ : ∀ n j, 0 < τ n j) (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n k => c n * ptrLosslessStackSeq (κ n) (τ n) (N n) k 0 0) XiC atTop) :
    ∀ᶠ n in atTop, ∀ j ≤ N n, τ n j ≤ Real.pi / 6 := by
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hsph : ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2), XiC z ≠ 0 := by
    intro z hz
    apply XiC_ne_zero_of_mem_closedBall_three
    have hc : (((6 : ℝ) : ℂ) / 2) = 3 := by push_cast; norm_num
    rw [hc, show (6 : ℝ) / 2 + 1 / 2 = 7 / 2 by norm_num] at hz
    exact sphere_subset_closedBall hz
  have hbudget := ptrLosslessStackSeq_eventually_budget κ τ N c hκ hτ hc hXiCd hconv
    (by norm_num : (0 : ℝ) < 6) (by norm_num : (0 : ℝ) < 1 / 2) hsph
  have hzero : (zeroSumBall XiC (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).re = 0 := by
    have := zeroSumBall_XiC_three
    push_cast at this ⊢
    rw [this, Complex.zero_re]
  filter_upwards [hbudget] with n hn
  intro j hj
  rw [hzero] at hn
  have hterm_nonneg : ∀ i : Fin (N n + 1),
      0 ≤ (((⌈(2 * τ n i) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) := by
    intro i
    have hx : 0 < (2 * τ n i) * 6 / (2 * Real.pi) := by
      have := hτ n i; positivity
    have : (1 : ℤ) ≤ ⌈(2 * τ n i) * 6 / (2 * Real.pi)⌉ := Int.one_le_ceil_iff.mpr hx
    have : (1 : ℝ) ≤ ((⌈(2 * τ n i) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  have hle := (Finset.single_le_sum (fun i _ => hterm_nonneg i)
    (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (N n + 1)))).trans hn
  have hceil : ⌈(2 * τ n j) * 6 / (2 * Real.pi)⌉ ≤ 1 := by
    have : ((⌈(2 * τ n j) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) ≤ 1 := by
      simpa using hle
    exact_mod_cast this
  have hx := Int.ceil_le.mp hceil
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_le_iff₀ (by positivity)] at hx
  push_cast at hx
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
  nlinarith

/-- **No lossless prime-log temporal stack converges to Ξ.** Slab durations
`log p ≥ log 2 > π/6` are excluded by the Ξ zero-free disc. -/
theorem not_tendsto_XiC_of_primeLog_losslessStacks
    (κ : ℕ → ℕ → ℝ) (p : ℕ → ℕ → Nat.Primes) (N : ℕ → ℕ) (c : ℕ → ℂ)
    (hκ : ∀ n j, 0 < κ n j) (hc : ∀ n, c n ≠ 0) :
    ¬ TendstoLocallyUniformly
      (fun n k => c n * ptrLosslessStackSeq (κ n)
        (fun j => Real.log ((p n j : ℕ) : ℝ)) (N n) k 0 0) XiC atTop := by
  intro hconv
  have hτ : ∀ n j, 0 < Real.log ((p n j : ℕ) : ℝ) := fun n j =>
    Real.log_pos (by exact_mod_cast (p n j).property.one_lt)
  obtain ⟨n, hn⟩ := (ptrLosslessStackSeq_slab_le_of_tendsto_XiC κ
    (fun n j => Real.log ((p n j : ℕ) : ℝ)) N c hκ hτ hc hconv).exists
  have h0 := hn 0 (Nat.zero_le _)
  have hlog2 : Real.log 2 ≤ Real.log ((p n 0 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (p n 0).property.two_le)
  have hl := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d2
  norm_num at hl hpi
  linarith

end

end RHTower
