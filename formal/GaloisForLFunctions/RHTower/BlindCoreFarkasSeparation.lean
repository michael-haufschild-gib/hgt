import GaloisForLFunctions.RHTower.CosDilationDivisorMomentPeriodizationRigidity
import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# Separating blind cores by the pole kernel and the Kelvin chirps

A blind core of width `L` is a smooth `f` supported in `[α, β] ⊂ (0, ∞)` with `β ≤ α e^L`,
`𝓜f(1) = 0` and `Ψ_f(n) = 0` for every `n ≥ 2` (`IsBlindCore`).  Its logarithmic autocorrelation
`b_f(v) = e^{v/2} A_f(e^v)` is supported in `[−L, L]`, and it is the additive autocorrelation of
`g(u) = √α e^{u/2} f(α e^u)`, which is supported in `[0, L]` (`autocorr_logPull`).

* `integral_kelvinChirp_mul_logAutocorr`: pairing `b_f` with the Kelvin chirp
  `φ_n(v) = e^{v/2} cos(2πn e^v) + e^{−v/2} cos(2πn e^{−v})` gives `Ψ_f(n)`; the chirp at `n = 0`
  is the pole kernel `2 cosh(v/2)` (`kelvinChirp_zero`).
* `closure_span_le_coreAnnihilator`: every functional on `C([−L, L])` in the closure, for pointwise
  convergence, of the span of the pole kernel and the chirps `φ_n`, `n ≥ 2`, vanishes on all blind
  cores of width `L`.
* `eq_zero_of_mem_closure_span_of_strictPD`: **separation.**  If such a functional is strictly
  positive on the autocorrelations of nonzero smooth functions supported in `[0, L]`, then every
  blind core of width `L` is zero.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace RHTower.BlindCoreFarkas

open ArchimedeanAnomaly ArchimedeanExactForm

noncomputable section

/-- The pole kernel `2 cosh(v/2)`. -/
def poleKernel (v : ℝ) : ℝ := 2 * Real.cosh (v / 2)

/-- The Kelvin chirp `φ_n(v) = e^{v/2} cos(2πn e^v) + e^{−v/2} cos(2πn e^{−v})`. -/
def kelvinChirp (n : ℕ) (v : ℝ) : ℝ :=
  Real.exp (v / 2) * Real.cos (2 * π * (n * Real.exp v)) +
    Real.exp (-v / 2) * Real.cos (2 * π * (n * Real.exp (-v)))

/-- The logarithmic autocorrelation `b_f(v) = e^{v/2} A_f(e^v)`. -/
def logAutocorr (f : ℝ → ℝ) (v : ℝ) : ℝ := Real.exp (v / 2) * dilationAutocorr f (Real.exp v)

/-- The logarithmic pull-back `g(u) = √α e^{u/2} f(α e^u)`. -/
def logPull (f : ℝ → ℝ) (α u : ℝ) : ℝ := Real.sqrt α * Real.exp (u / 2) * f (α * Real.exp u)

theorem kelvinChirp_zero : kelvinChirp 0 = poleKernel := by
  funext v
  simp only [kelvinChirp, poleKernel, Nat.cast_zero, zero_mul, mul_zero, Real.cos_zero, mul_one,
    Real.cosh_eq]
  rw [neg_div]
  ring

variable {f : ℝ → ℝ} {α β : ℝ}

/-- `∫_ℝ α e^u H(α e^u) du = ∫_0^∞ H`. -/
theorem integral_mul_exp_comp (H : ℝ → ℝ) (hα : 0 < α) :
    ∫ u, α * Real.exp u * H (α * Real.exp u) = ∫ y in Ioi (0 : ℝ), H y := by
  have h := GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp fun z => α * H (α * z)
  rw [integral_const_mul, integral_comp_mul_left_Ioi H 0 hα, mul_zero, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul] at h
  rw [h]
  exact integral_congr_ae (Eventually.of_forall fun u => by ring)

/-- **`b_f` is the autocorrelation of the logarithmic pull-back.** -/
theorem autocorr_logPull (hα : 0 < α) (v : ℝ) : autocorr (logPull f α) v = logAutocorr f v := by
  have hpt : ∀ u, logPull f α u * logPull f α (u + v) =
      Real.exp (v / 2) * (α * Real.exp u * (f (α * Real.exp u) * f (Real.exp v * (α * Real.exp u)))) := by
    intro u
    have hs : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
    have he : Real.exp (u / 2) * Real.exp ((u + v) / 2) = Real.exp u * Real.exp (v / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have he2 : α * Real.exp (u + v) = Real.exp v * (α * Real.exp u) := by rw [Real.exp_add]; ring
    simp only [logPull]
    rw [he2]
    linear_combination (f (α * Real.exp u) * f (Real.exp v * (α * Real.exp u))) *
      (Real.exp (u / 2) * Real.exp ((u + v) / 2) * (hs) + α * he)
  rw [autocorr]
  simp_rw [hpt]
  rw [integral_const_mul, integral_mul_exp_comp (fun y => f y * f (Real.exp v * y)) hα]
  rfl

theorem logPull_eq_zero (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {u : ℝ}
    (hu : u < 0 ∨ Real.log (β / α) < u) : logPull f α u = 0 := by
  have hz : f (α * Real.exp u) = 0 := by
    by_contra h
    obtain ⟨h1, h2⟩ := hsupp _ h
    rcases hu with hu | hu
    · have he : Real.exp u < 1 := by
        have := Real.exp_lt_exp.mpr hu
        rwa [Real.exp_zero] at this
      have : α * Real.exp u < α := by nlinarith
      linarith
    · have hβ : 0 < β := hα.trans_le (h1.trans h2)
      have : β < α * Real.exp u := by
        rw [Real.log_lt_iff_lt_exp (div_pos hβ hα), div_lt_iff₀ hα] at hu
        linarith
      linarith
  simp [logPull, hz]

theorem contDiff_logPull (hf : ContDiff ℝ ∞ f) (α : ℝ) : ContDiff ℝ ∞ (logPull f α) := by
  unfold logPull
  exact (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))).mul
    (hf.comp (contDiff_const.mul Real.contDiff_exp))

/-! ### Support and the chirp pairing -/

theorem logAutocorr_eq_zero (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    {v : ℝ} (hv : v ∉ Icc (Real.log (α / β)) (Real.log (β / α))) : logAutocorr f v = 0 := by
  have hβ : 0 < β := hα.trans_le hαβ
  rw [logAutocorr, dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp, mul_zero]
  intro hr
  apply hv
  exact ⟨(Real.log_le_iff_le_exp (div_pos hα hβ)).mpr hr.1,
    (Real.le_log_iff_exp_le (div_pos hβ hα)).mpr hr.2⟩

theorem continuous_logAutocorr (hf : Continuous f) (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) : Continuous (logAutocorr f) :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    ((continuous_dilationAutocorr hf hα hsupp).comp Real.continuous_exp)

theorem hasCompactSupport_logAutocorr_mul (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (κ : ℝ → ℝ) :
    HasCompactSupport fun v => κ v * logAutocorr f v :=
  HasCompactSupport.intro (isCompact_Icc (a := Real.log (α / β)) (b := Real.log (β / α)))
    fun v hv => by rw [logAutocorr_eq_zero hα hαβ hsupp hv, mul_zero]

/-- **Pairing with the Kelvin chirp gives the cosine–dilation kernel**:
`∫ φ_n(v) b_f(v) dv = Ψ_f(n)`. -/
theorem integral_kelvinChirp_mul_logAutocorr (hf : Continuous f) (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (n : ℕ) :
    ∫ v, kelvinChirp n v * logAutocorr f v = cosDilationKernel f n := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hAc : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hA0 : ∀ v, v ∉ Icc (Real.log (α / β)) (Real.log (β / α)) →
      dilationAutocorr f (Real.exp v) = 0 := fun v hv => by
    refine dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun hr => hv ⟨?_, ?_⟩
    · exact (Real.log_le_iff_le_exp (div_pos hα hβ)).mpr hr.1
    · exact (Real.le_log_iff_exp_le (div_pos hβ hα)).mpr hr.2
  set T1 : ℝ → ℝ := fun v => Real.exp v *
    (dilationAutocorr f (Real.exp v) * Real.cos (2 * π * (n * Real.exp v))) with hT1
  set T2 : ℝ → ℝ := fun v =>
    dilationAutocorr f (Real.exp v) * Real.cos (2 * π * (n * Real.exp (-v))) with hT2
  have hpt : ∀ v, kelvinChirp n v * logAutocorr f v = T1 v + T2 v := fun v => by
    simp only [kelvinChirp, logAutocorr, hT1, hT2]
    have e1 : Real.exp (v / 2) * Real.exp (v / 2) = Real.exp v := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-v / 2) * Real.exp (v / 2) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]; ring_nf
    linear_combination (dilationAutocorr f (Real.exp v) * Real.cos (2 * π * (n * Real.exp v))) * e1 +
      (dilationAutocorr f (Real.exp v) * Real.cos (2 * π * (n * Real.exp (-v)))) * e2
  have hcs : ∀ T : ℝ → ℝ, (∀ v, dilationAutocorr f (Real.exp v) = 0 → T v = 0) →
      HasCompactSupport T := fun T hT =>
    HasCompactSupport.intro (isCompact_Icc (a := Real.log (α / β)) (b := Real.log (β / α)))
      fun v hv => hT v (hA0 v hv)
  have hi1 : Integrable T1 := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hcs T1 fun v h => by simp [hT1, h])
    simp only [hT1]
    fun_prop
  have hi2 : Integrable T2 := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hcs T2 fun v h => by simp [hT2, h])
    simp only [hT2]
    fun_prop
  have hsym : ∫ v, T2 v = ∫ v, T1 v := by
    rw [← integral_neg_eq_self T2 volume]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hT1, hT2, neg_neg]
    rw [Real.exp_neg, dilationAutocorr_inv f (Real.exp_pos v)]
    ring
  have hT1int : ∫ v, T1 v =
      ∫ r in Ioi (0 : ℝ), dilationAutocorr f r * Real.cos (2 * π * (n * r)) :=
    (GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp
      fun r => dilationAutocorr f r * Real.cos (2 * π * (n * r))).symm
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hi1 hi2, hsym, hT1int,
    cosDilationKernel_eq hf hα hαβ hsupp]
  ring

/-! ### Blind cores and the functionals annihilating them -/

/-- A **blind core of width `L`**: smooth, supported in `[α, β]` with `0 < α ≤ β ≤ α e^L`,
`𝓜f(1) = 0`, and `Ψ_f(n) = 0` for every `n ≥ 2`. -/
def IsBlindCore (L : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧
    (∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ β ≤ α * Real.exp L ∧ ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) ∧
    mellin (fun y : ℝ => (f y : ℂ)) 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0

theorem IsBlindCore.continuous_logAutocorr {L : ℝ} (h : IsBlindCore L f) :
    Continuous (logAutocorr f) := by
  obtain ⟨hf, ⟨α, β, hα, -, -, hsupp⟩, -, -⟩ := h
  exact RHTower.BlindCoreFarkas.continuous_logAutocorr hf.continuous hα hsupp

theorem log_div_le_of_le_mul_exp {L : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβL : β ≤ α * Real.exp L) :
    Real.log (β / α) ≤ L := by
  have hβ : 0 < β := hα.trans_le hαβ
  rw [Real.log_le_iff_le_exp (div_pos hβ hα), div_le_iff₀ hα]
  linarith [mul_comm α (Real.exp L)]

theorem IsBlindCore.logAutocorr_eq_zero {L : ℝ} (h : IsBlindCore L f) {v : ℝ}
    (hv : v ∉ Icc (-L) L) : logAutocorr f v = 0 := by
  obtain ⟨-, ⟨α, β, hα, hαβ, hβL, hsupp⟩, -, -⟩ := h
  have hβ : 0 < β := hα.trans_le hαβ
  have h1 := log_div_le_of_le_mul_exp hα hαβ hβL
  have h2 : Real.log (α / β) = -Real.log (β / α) := by rw [← Real.log_inv, inv_div]
  refine RHTower.BlindCoreFarkas.logAutocorr_eq_zero hα hαβ hsupp fun hv' => hv ⟨?_, ?_⟩
  · linarith [hv'.1]
  · linarith [hv'.2]

/-- The restriction of a continuous function to `[−L, L]`. -/
def restr (L : ℝ) (b : ℝ → ℝ) (hb : Continuous b) : C(Icc (-L) L, ℝ) :=
  ⟨fun v => b v, hb.comp continuous_subtype_val⟩

/-- The functional `b ↦ ∫_{−L}^{L} κ b` on `C([−L, L])`. -/
def kernelFunctional {L : ℝ} (hL : -L ≤ L) (κ : ℝ → ℝ) (b : C(Icc (-L) L, ℝ)) : ℝ :=
  ∫ v in Icc (-L) L, κ v * Set.IccExtend hL b v

/-- The functionals on `C([−L, L])` vanishing on the logarithmic autocorrelation of every blind
core of width `L`. -/
def coreAnnihilator (L : ℝ) : Submodule ℝ (C(Icc (-L) L, ℝ) → ℝ) where
  carrier := {T | ∀ f (h : IsBlindCore L f),
    T (restr L (logAutocorr f) h.continuous_logAutocorr) = 0}
  add_mem' := fun ha hb f h => by simp [ha f h, hb f h]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c T hT f h => by simp [hT f h]

theorem mem_coreAnnihilator {L : ℝ} {T : C(Icc (-L) L, ℝ) → ℝ} :
    T ∈ coreAnnihilator L ↔
      ∀ f (h : IsBlindCore L f), T (restr L (logAutocorr f) h.continuous_logAutocorr) = 0 :=
  Iff.rfl

/-- The annihilator is closed for pointwise convergence of functionals. -/
theorem isClosed_coreAnnihilator (L : ℝ) :
    IsClosed (coreAnnihilator L : Set (C(Icc (-L) L, ℝ) → ℝ)) := by
  have e : (coreAnnihilator L : Set (C(Icc (-L) L, ℝ) → ℝ)) = ⋂ f, ⋂ h : IsBlindCore L f,
      {T | T (restr L (logAutocorr f) h.continuous_logAutocorr) = 0} := by
    ext T
    simp only [SetLike.mem_coe, mem_coreAnnihilator, mem_iInter, mem_setOf_eq]
  rw [e]
  exact isClosed_iInter fun f => isClosed_iInter fun h =>
    isClosed_eq (continuous_apply _) continuous_const

theorem kernelFunctional_restr {L : ℝ} (hL : -L ≤ L) (κ : ℝ → ℝ) {b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ v, v ∉ Icc (-L) L → b v = 0) :
    kernelFunctional hL κ (restr L b hb) = ∫ v, κ v * b v := by
  unfold kernelFunctional
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun v => κ v * b v) fun v hv => by
    simp only
    rw [Set.IccExtend_of_mem hL _ hv]
    rfl]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by rw [hb0 v hv, mul_zero]

/-- The pole kernel (`n = 0`) and the chirps `φ_n`, `n ≥ 2`, annihilate every blind core. -/
theorem kernelFunctional_kelvinChirp_mem {L : ℝ} (hL : -L ≤ L) {n : ℕ} (hn : n = 0 ∨ 2 ≤ n) :
    kernelFunctional hL (kelvinChirp n) ∈ coreAnnihilator L := by
  refine mem_coreAnnihilator.mpr fun f h => ?_
  rw [kernelFunctional_restr hL _ h.continuous_logAutocorr fun v hv => h.logAutocorr_eq_zero hv]
  obtain ⟨hf, ⟨α, β, hα, hαβ, -, hsupp⟩, h0, hb⟩ := h
  rw [integral_kelvinChirp_mul_logAutocorr hf.continuous hα hαβ hsupp n]
  rcases hn with rfl | hn
  · simpa using cosDilationKernel_zero_eq_zero_of_mellin_one_eq_zero h0
  · exact hb n hn

/-- The pole kernel and the Kelvin chirps `φ_n`, `n ≥ 2`, as functionals on `C([−L, L])`. -/
def chirpFunctionals {L : ℝ} (hL : -L ≤ L) : Set (C(Icc (-L) L, ℝ) → ℝ) :=
  {T | ∃ n : ℕ, (n = 0 ∨ 2 ≤ n) ∧ T = kernelFunctional hL (kelvinChirp n)}

/-- **Every functional in the closed span of the pole kernel and the chirps annihilates the blind
cores** (closure for pointwise convergence on `C([−L, L])`, which contains the weak-* closure). -/
theorem closure_span_le_coreAnnihilator {L : ℝ} (hL : -L ≤ L) :
    closure (Submodule.span ℝ (chirpFunctionals hL) : Set (C(Icc (-L) L, ℝ) → ℝ)) ⊆
      coreAnnihilator L :=
  closure_minimal (SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr
    fun _ ⟨_, hn, hT⟩ => hT ▸ kernelFunctional_kelvinChirp_mem hL hn))
    (isClosed_coreAnnihilator L)

theorem continuous_kelvinChirp (n : ℕ) : Continuous (kelvinChirp n) := by
  unfold kelvinChirp
  fun_prop

/-- A finite combination of the pole kernel and the chirps `φ_n`, `n ≥ 2`, defines a functional
in their span. -/
theorem kernelFunctional_sum_mem_span {L : ℝ} (hL : -L ≤ L) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n = 0 ∨ 2 ≤ n) (c : ℕ → ℝ) :
    kernelFunctional hL (fun v => ∑ n ∈ s, c n * kelvinChirp n v) ∈
      Submodule.span ℝ (chirpFunctionals hL) := by
  have e : kernelFunctional hL (fun v => ∑ n ∈ s, c n * kelvinChirp n v) =
      ∑ n ∈ s, c n • kernelFunctional hL (kelvinChirp n) := by
    funext b
    have hib : ∀ n ∈ s, IntegrableOn (fun v => c n * kelvinChirp n v * Set.IccExtend hL b v)
        (Icc (-L) L) := fun n _ =>
      (((continuous_const.mul (continuous_kelvinChirp n)).mul
        (b.continuous.comp continuous_projIcc)).continuousOn).integrableOn_Icc
    simp only [kernelFunctional, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [integral_finsetSum s hib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  rw [e]
  exact Submodule.sum_mem _ fun n hn =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hs n hn, rfl⟩)

/-! ### Separation -/

/-- `T` is **strictly positive definite at width `L`**: positive on the autocorrelation of every
nonzero smooth function supported in `[0, L]`. -/
def StrictPD (L : ℝ) (T : C(Icc (-L) L, ℝ) → ℝ) : Prop :=
  ∀ g : ℝ → ℝ, ∀ hg : ContDiff ℝ ∞ g, ∀ hsupp : (∀ u, g u ≠ 0 → 0 ≤ u ∧ u ≤ L), (∃ u, g u ≠ 0) →
    0 < T (restr L (autocorr g) (continuous_autocorr (hg.of_le (WithTop.coe_le_coe.mpr le_top))
      (HasCompactSupport.intro (isCompact_Icc (a := 0) (b := L)) fun u hu => by
        by_contra h
        exact hu (hsupp u h))))

/-- A strictly positive definite annihilating functional rules out blind cores of width `L`. -/
theorem eq_zero_of_mem_coreAnnihilator_of_strictPD {L : ℝ} {T : C(Icc (-L) L, ℝ) → ℝ}
    (hT : T ∈ coreAnnihilator L) (hpd : StrictPD L T) {f : ℝ → ℝ} (h : IsBlindCore L f) (y : ℝ) :
    f y = 0 := by
  by_contra hy₀
  have hz := mem_coreAnnihilator.mp hT f h
  obtain ⟨hf, ⟨α, β, hα, hαβ, hβL, hsupp⟩, -, -⟩ := id h
  have hlog := log_div_le_of_le_mul_exp hα hαβ hβL
  have hgs : ∀ u, logPull f α u ≠ 0 → 0 ≤ u ∧ u ≤ L := fun u hu => by
    by_contra hc
    apply hu
    refine logPull_eq_zero hα hsupp ?_
    rcases not_and_or.mp hc with h1 | h1
    · exact Or.inl (not_le.mp h1)
    · exact Or.inr (lt_of_le_of_lt hlog (not_le.mp h1))
  have hgne : ∃ u, logPull f α u ≠ 0 := by
    have hy := hsupp y hy₀
    have hy0 : 0 < y := hα.trans_le hy.1
    refine ⟨Real.log (y / α), ?_⟩
    have e : α * Real.exp (Real.log (y / α)) = y := by
      rw [Real.exp_log (div_pos hy0 hα)]
      field_simp
    simp only [logPull, e]
    exact mul_ne_zero (mul_ne_zero (Real.sqrt_pos.mpr hα).ne' (Real.exp_pos _).ne') hy₀
  have hpos := hpd _ (contDiff_logPull hf α) hgs hgne
  have heq : ∀ h1 h2, restr L (autocorr (logPull f α)) h1 = restr L (logAutocorr f) h2 :=
    fun _ _ => ContinuousMap.ext fun v => autocorr_logPull hα v
  rw [heq _ h.continuous_logAutocorr, hz] at hpos
  exact lt_irrefl 0 hpos

/-- **Separation of blind cores** (the exact direction of the Farkas duality).  If a functional in
the closed span of the pole kernel and the Kelvin chirps `φ_n`, `n ≥ 2`, is strictly positive
definite at width `L`, then every blind core of width `L` vanishes. -/
theorem eq_zero_of_mem_closure_span_of_strictPD {L : ℝ} (hL : -L ≤ L)
    {T : C(Icc (-L) L, ℝ) → ℝ}
    (hT : T ∈ closure (Submodule.span ℝ (chirpFunctionals hL) : Set (C(Icc (-L) L, ℝ) → ℝ)))
    (hpd : StrictPD L T) {f : ℝ → ℝ} (h : IsBlindCore L f) (y : ℝ) : f y = 0 :=
  eq_zero_of_mem_coreAnnihilator_of_strictPD (closure_span_le_coreAnnihilator hL hT) hpd h y

/-- **Kernel form**: a finite combination `κ = Σ c_n φ_n` (`n = 0` the pole kernel, `n ≥ 2` the
Kelvin chirps) whose functional is strictly positive definite at width `L` rules out blind cores of
width `L`. -/
theorem eq_zero_of_kernel_strictPD {L : ℝ} (hL : -L ≤ L) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n = 0 ∨ 2 ≤ n) (c : ℕ → ℝ)
    (hpd : StrictPD L (kernelFunctional hL fun v => ∑ n ∈ s, c n * kelvinChirp n v))
    {f : ℝ → ℝ} (h : IsBlindCore L f) (y : ℝ) : f y = 0 :=
  eq_zero_of_mem_closure_span_of_strictPD hL
    (subset_closure (kernelFunctional_sum_mem_span hL s hs c)) hpd h y

end

end RHTower.BlindCoreFarkas
