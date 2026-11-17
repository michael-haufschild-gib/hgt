import GaloisForLFunctions.ExclusionOfTheCriticalState.WeilsFormOnProbesIsTheCaratheodoryKernelOfXi
import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation
import GaloisForLFunctions.HTGeometry.PSDKernelMatrixBridge
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Real probe nodes decide the Riemann hypothesis

Weil's bare form on two half-line probes `e_p = 1_{u<0} e^{pu}` is the Carathéodory kernel
`K(p, q) = (D(p) + D(q))/(p + q)` of `D = (log ξ)'(½ + ·)`
(`bareMixedEnergy_probe_eq_criticalLogDerivKernel`). RH is positivity of `K` on the complex half
plane `Re p > ½`. Here the nodes are real and sparse.

* **Uniqueness sets** (`IsProbeUniquenessSet`). A set `S` of reals is one if every bounded
  holomorphic function on `Re w > ½` vanishing on `S` vanishes identically: any set with an
  accumulation point in `(½, ∞)` (`isProbeUniquenessSet_of_frequently`), every interval
  (`isProbeUniquenessSet_Ioo`), every Blaschke-divergent sequence tending to `∞`
  (`isProbeUniquenessSet_of_blaschke`), the integers `n ≥ 5` (`isProbeUniquenessSet_natFrom`).
* **The probe form of RH** (`riemannHypothesis_iff_probe_forms_nonneg`). On every uniqueness set
  `S ⊆ (½, ∞)`: RH ⇔ every real Pick matrix `(K(p_i, p_j))` with nodes in `S` is positive
  semidefinite, that is, Weil's bare form is nonnegative on the real span of the probes `e_p`,
  `p ∈ S`. Mechanism: a positive Pick matrix family has a Carathéodory interpolant `G` on
  `Re p > 0` (Nevanlinna–Pick); the Cayley transforms of `G` and of `D` (`Re D > 0` on
  `Re p > ½` unconditionally) are bounded there and agree on `S`, so `G = D` on `Re p > ½`
  and `K` is positive on the whole half plane.
* **The integer criterion** (`riemannHypothesis_iff_integer_pick_nonneg`). RH ⇔ the infinite
  matrix `((D(m) + D(n))/(m + n))_{m,n ≥ 5}` is positive semidefinite, with the explicit symbol
  `D(p) = 1/(p+½) + 1/(p−½) + (Re ψ(¼+p/2) − log π)/2 − Σ Λ(k) k^{−½−p}`. The probes `e_n`,
  `n ≥ 5`, lie in the energy domain of the critical state.
-/

noncomputable section
open Complex Set Filter Topology
open scoped ComplexConjugate ComplexOrder Matrix

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry _root_.RHTower

/-! ### Uniqueness sets of real nodes -/

/-- A set of real nodes on which bounded holomorphic functions of `Re w > ½` are determined. -/
def IsProbeUniquenessSet (S : Set ℝ) : Prop :=
  ∀ G : ℂ → ℂ, DifferentiableOn ℂ G {w : ℂ | 1 / 2 < w.re} →
    (∃ C : ℝ, ∀ w : ℂ, 1 / 2 < w.re → ‖G w‖ ≤ C) →
    (∀ p ∈ S, G (p : ℂ) = 0) → ∀ w : ℂ, 1 / 2 < w.re → G w = 0

theorem IsProbeUniquenessSet.nonempty {S : Set ℝ} (hS : IsProbeUniquenessSet S) :
    S.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have h1 := hS (fun _ => 1) (differentiableOn_const _) ⟨1, fun _ _ => by simp⟩
    (by simp [h]) 1 (by norm_num)
  exact one_ne_zero h1

theorem IsProbeUniquenessSet.mono {S T : Set ℝ} (hS : IsProbeUniquenessSet S) (hST : S ⊆ T) :
    IsProbeUniquenessSet T :=
  fun G hG hb hz => hS G hG hb fun p hp => hz p (hST hp)

/-- A set accumulating at a point of `(½, ∞)` is a uniqueness set (identity theorem). -/
theorem isProbeUniquenessSet_of_frequently {S : Set ℝ} {x₀ : ℝ} (hx₀ : 1 / 2 < x₀)
    (hacc : ∃ᶠ x in 𝓝[≠] x₀, x ∈ S) : IsProbeUniquenessSet S := by
  intro G hG _ hz w hw
  have hU : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticOnNhd ℂ G {w : ℂ | 1 / 2 < w.re} := hG.analyticOnNhd hU
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using hx)
  have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), G z = (fun _ : ℂ => (0 : ℂ)) z :=
    ht.frequently (hacc.mono fun x hx => hz x hx)
  exact hana.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected (by simpa using hx₀) hfreq hw

/-- Every open interval of exponents beyond `½` is a uniqueness set. -/
theorem isProbeUniquenessSet_Ioo {α β : ℝ} (hα : 1 / 2 ≤ α) (hαβ : α < β) :
    IsProbeUniquenessSet (Ioo α β) := by
  have hmem : Ioo α β ∈ 𝓝 ((α + β) / 2) := Ioo_mem_nhds (by linarith) (by linarith)
  exact isProbeUniquenessSet_of_frequently (x₀ := (α + β) / 2) (by linarith)
    (eventually_nhdsWithin_of_eventually_nhds hmem).frequently

/-- A Blaschke-divergent real sequence tending to `∞` is a uniqueness set. -/
theorem isProbeUniquenessSet_of_blaschke {S : Set ℝ} {κ : Type*} {Λ : κ → ℝ}
    (hinj : Function.Injective Λ) (htend : Tendsto Λ cofinite atTop) (hpos : ∀ j, 1 / 2 < Λ j)
    (hmem : ∀ j, Λ j ∈ S) (hdiv : ¬ Summable fun j => Λ j / (1 + Λ j ^ 2)) :
    IsProbeUniquenessSet S := by
  rintro G hG ⟨C, hC⟩ hz
  exact eqOn_zero_of_bounded_of_blaschke_divergent (by norm_num) hG hC hinj htend hpos
    (fun j => hz _ (hmem j)) hdiv

/-- The integers `n ≥ N`, `N ≥ 1`, form a uniqueness set. -/
theorem isProbeUniquenessSet_natFrom {N : ℕ} (hN : 1 ≤ N) :
    IsProbeUniquenessSet {p : ℝ | ∃ n : ℕ, N ≤ n ∧ p = n} := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine isProbeUniquenessSet_of_blaschke (Λ := fun n : ℕ => ((n + N : ℕ) : ℝ)) ?_ ?_ ?_ ?_ ?_
  · intro a b h
    have := Nat.cast_injective (R := ℝ) h
    omega
  · rw [Nat.cofinite_eq_atTop]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N)
  · intro n
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro n
    exact ⟨n + N, by omega, rfl⟩
  · intro hs
    have hle : ∀ n : ℕ, (1 : ℝ) / ((n + N : ℕ) : ℝ) ≤
        2 * (((n + N : ℕ) : ℝ) / (1 + ((n + N : ℕ) : ℝ) ^ 2)) := by
      intro n
      have hx : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsum : Summable fun n : ℕ => (1 : ℝ) / ((n + N : ℕ) : ℝ) :=
      Summable.of_nonneg_of_le (fun n => by positivity) hle (hs.mul_left 2)
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff N).mp hsum)

/-! ### Real symmetric kernels -/

/-- A real symmetric kernel all of whose real quadratic forms are nonnegative is a positive
semidefinite complex kernel: the imaginary parts of a complex vector contribute a second real
form. -/
theorem isPSDKernel_ofReal_of_forall_real {X : Type*} {K : X → X → ℝ}
    (hsym : ∀ x y, K x y = K y x)
    (h : ∀ (n : ℕ) (w : Fin n → X) (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K (w i) (w j)) :
    IsPSDKernel (fun x y => (K x y : ℂ)) := by
  refine isPSDKernel_of_forall_posSemidef (fun x y => by rw [Complex.conj_ofReal, hsym])
    fun n w => Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, hsym]
  · have key : dotProduct (star v) (Matrix.mulVec (Matrix.of fun j k => (K (w j) (w k) : ℂ)) v) =
        ∑ i, ∑ j, star (v i) * ((K (w i) (w j) : ℂ) * v j) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [key, Complex.nonneg_iff]
    simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero, neg_mul, sub_neg_eq_add]
    constructor
    · have h1 := h n w fun i => (v i).re
      have h2 := h n w fun i => (v i).im
      have e : ∑ i, ∑ j, ((v i).re * (K (w i) (w j) * (v j).re) +
          (v i).im * (K (w i) (w j) * (v j).im)) =
          (∑ i, ∑ j, (v i).re * (v j).re * K (w i) (w j)) +
            ∑ i, ∑ j, (v i).im * (v j).im * K (w i) (w j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    · have e : ∑ i, ∑ j, ((v i).re * (K (w i) (w j) * (v j).im) +
          -((v i).im * (K (w i) (w j) * (v j).re))) = 0 := by
        simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
        rw [add_neg_eq_zero, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsym]
        ring
      exact e.symm

/-! ### The probe kernel on real nodes -/

theorem bareMixedEnergy_probe_symm {p q : ℝ} (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    bareMixedEnergy (probe p) (probe q) = bareMixedEnergy (probe q) (probe p) := by
  rw [bareMixedEnergy_probe hp hq, bareMixedEnergy_probe hq hp, add_comm (probeSymbol p),
    add_comm p]

/-- **RH gives every real Pick matrix of the probe kernel.** -/
theorem probe_forms_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {n : ℕ}
    (p c : Fin n → ℝ) (hp : ∀ i, 1 / 2 < p i) :
    0 ≤ ∑ i, ∑ j, c i * c j * bareMixedEnergy (probe (p i)) (probe (p j)) := by
  have hK := (riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel (a := 1 / 2) le_rfl).mp hRH
  have hM := (hK.posSemidef fun i =>
    (⟨((p i : ℝ) : ℂ), by simpa using hp i⟩ : {W : ℂ // 1 / 2 < W.re})).dotProduct_mulVec_nonneg
      fun i => ((c i : ℝ) : ℂ)
  have hval : dotProduct (star fun i => ((c i : ℝ) : ℂ)) (Matrix.mulVec (Matrix.of fun j k =>
      criticalLogDerivKernel ((p j : ℝ) : ℂ) ((p k : ℝ) : ℂ)) fun i => ((c i : ℝ) : ℂ)) =
      ((∑ i, ∑ j, c i * c j * bareMixedEnergy (probe (p i)) (probe (p j)) : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [bareMixedEnergy_probe_eq_criticalLogDerivKernel (hp i) (hp j)]
    ring
  exact Complex.zero_le_real.mp (hval ▸ hM)

/-- **Positive real Pick matrices on a uniqueness set give RH.** The Carathéodory interpolant of
the nodes agrees with `D = (log ξ)'(½ + ·)` on the whole half plane `Re p > ½`. -/
theorem riemannHypothesis_of_probe_forms_nonneg {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p)
    (hU : IsProbeUniquenessSet S)
    (h : ∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) →
      0 ≤ ∑ i, ∑ j, c i * c j * bareMixedEnergy (probe (p i)) (probe (p j))) :
    RiemannHypothesis := by
  set D : ℂ → ℂ := logDeriv xiCent with hDdef
  -- the real Pick kernel on `S` is positive semidefinite and is the Carathéodory kernel of `D`
  have hK : IsPSDKernel (fun x y : S =>
      ((bareMixedEnergy (probe (x : ℝ)) (probe (y : ℝ)) : ℝ) : ℂ)) :=
    isPSDKernel_ofReal_of_forall_real (fun x y => bareMixedEnergy_probe_symm (hS x x.2) (hS y y.2))
      fun n w c => h n (fun i => (w i : ℝ)) c fun i => (w i).2
  haveI : Nonempty S := hU.nonempty.to_subtype
  obtain ⟨G, hGd, hGre, hGeq⟩ := exists_caratheodory_interpolant (X := S)
    (fun x => (((x : ℝ)) : ℂ)) (fun x => D ((x : ℝ) : ℂ))
    (fun x => by simpa using (by linarith [hS x x.2] : (0 : ℝ) < x))
    (hK.congr fun x y => by
      rw [bareMixedEnergy_probe_eq_criticalLogDerivKernel (hS x x.2) (hS y y.2)]
      rfl)
  have hopen0 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGat : ∀ u : ℂ, 0 < u.re → DifferentiableAt ℂ G u :=
    fun u hu => hGd.differentiableAt (hopen0.mem_nhds hu)
  have hGre' : ∀ w : ℂ, 1 / 2 < w.re → 0 ≤ (G w).re := fun w hw => hGre w (by linarith)
  have hDre : ∀ w : ℂ, 1 / 2 < w.re → 0 ≤ (D w).re := fun w hw => (re_logDeriv_xiCent_pos hw).le
  -- the Cayley transforms of `G` and `D` are bounded on `Re w > ½` and agree on `S`
  have hcay : ∀ w : ℂ, 1 / 2 < w.re → cayleyRight (G w) - cayleyRight (D w) = 0 := by
    refine hU (fun w => cayleyRight (G w) - cayleyRight (D w)) ?_ ⟨2, fun w hw => ?_⟩ ?_
    · intro w hw
      have hw' : 1 / 2 < w.re := hw
      have hG1 := add_one_ne_zero_of_re_nonneg (hGre' w hw')
      have hD1 := add_one_ne_zero_of_re_nonneg (hDre w hw')
      have hGw := hGat w (by linarith)
      have hDw := differentiableAt_logDeriv_xiCent hw'
      show DifferentiableWithinAt ℂ
        (fun w => (G w - 1) / (G w + 1) - (D w - 1) / (D w + 1)) _ w
      exact (((hGw.sub_const 1).div (hGw.add_const 1) hG1).sub
        ((hDw.sub_const 1).div (hDw.add_const 1) hD1)).differentiableWithinAt
    · calc ‖cayleyRight (G w) - cayleyRight (D w)‖
          ≤ ‖cayleyRight (G w)‖ + ‖cayleyRight (D w)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (norm_cayleyRight_le_one (hGre' w hw))
            (norm_cayleyRight_le_one (hDre w hw))
        _ = 2 := by norm_num
    · intro p hp
      have := hGeq ⟨p, hp⟩
      simp only at this
      rw [this, sub_self]
  have hGD : ∀ w : ℂ, 1 / 2 < w.re → G w = D w := fun w hw => by
    rw [← cayleyRight_inv (hGre' w hw), ← cayleyRight_inv (hDre w hw),
      sub_eq_zero.mp (hcay w hw)]
  -- the critical kernel is the Carathéodory kernel of `G` on `Re w > ½`
  have hpsd := (isPSDKernel_halfPlaneCaratheodory hGat fun u hu => hGre u hu).comp
    fun x : {W : ℂ // 1 / 2 < W.re} => (⟨(x : ℂ), by linarith [x.2]⟩ : {u : ℂ // 0 < u.re})
  refine (riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel (a := 1 / 2) le_rfl).mpr
    (hpsd.congr fun x y => ?_)
  simp only
  rw [hGD _ x.2, hGD _ y.2]
  rfl

/-- **The probe form of RH.** On every uniqueness set `S ⊆ (½, ∞)` of probe exponents, RH holds
iff Weil's bare form is nonnegative on the real span of the probes `e_p`, `p ∈ S`. -/
theorem riemannHypothesis_iff_probe_forms_nonneg {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p)
    (hU : IsProbeUniquenessSet S) :
    RiemannHypothesis ↔ ∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) →
      0 ≤ ∑ i, ∑ j, c i * c j * bareMixedEnergy (probe (p i)) (probe (p j)) :=
  ⟨fun hRH _ p c hp => probe_forms_nonneg_of_riemannHypothesis hRH p c fun i => hS _ (hp i),
    riemannHypothesis_of_probe_forms_nonneg hS hU⟩

/-- RH is decided by the probes with exponents in any interval `(α, β)`, `½ ≤ α < β`. -/
theorem riemannHypothesis_iff_probe_forms_nonneg_Ioo {α β : ℝ} (hα : 1 / 2 ≤ α) (hαβ : α < β) :
    RiemannHypothesis ↔ ∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ Ioo α β) →
      0 ≤ ∑ i, ∑ j, c i * c j * bareMixedEnergy (probe (p i)) (probe (p j)) :=
  riemannHypothesis_iff_probe_forms_nonneg (fun _ hp => lt_of_le_of_lt hα hp.1)
    (isProbeUniquenessSet_Ioo hα hαβ)

/-- **The integer Pick criterion.** RH holds iff the matrix `((D(m) + D(n))/(m + n))_{m,n ≥ 5}` of
the explicit probe symbol is positive semidefinite. -/
theorem riemannHypothesis_iff_integer_pick_nonneg :
    RiemannHypothesis ↔ ∀ (n : ℕ) (k : Fin n → ℕ) (c : Fin n → ℝ), (∀ i, 5 ≤ k i) →
      0 ≤ ∑ i, ∑ j, c i * c j *
        ((probeSymbol (k i) + probeSymbol (k j)) / ((k i : ℝ) + (k j : ℝ))) := by
  have hS : ∀ p ∈ {p : ℝ | ∃ m : ℕ, 5 ≤ m ∧ p = m}, 1 / 2 < p := by
    rintro p ⟨m, hm, rfl⟩
    have : (5 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hk : ∀ m : ℕ, 5 ≤ m → (1 / 2 : ℝ) < m := fun m hm => hS m ⟨m, hm, rfl⟩
  rw [riemannHypothesis_iff_probe_forms_nonneg hS (isProbeUniquenessSet_natFrom (by norm_num))]
  constructor
  · intro h n k c hk5
    have := h n (fun i => (k i : ℝ)) c fun i => ⟨k i, hk5 i, rfl⟩
    refine this.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [bareMixedEnergy_probe (hk _ (hk5 i)) (hk _ (hk5 j))]
  · intro h n p c hp
    choose k hk5 hpk using hp
    have := h n k c hk5
    refine this.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [hpk i, hpk j, bareMixedEnergy_probe (hk _ (hk5 i)) (hk _ (hk5 j))]

#print axioms riemannHypothesis_iff_probe_forms_nonneg
#print axioms riemannHypothesis_iff_integer_pick_nonneg

end GaloisForLFunctions.ExclusionOfTheCriticalState
