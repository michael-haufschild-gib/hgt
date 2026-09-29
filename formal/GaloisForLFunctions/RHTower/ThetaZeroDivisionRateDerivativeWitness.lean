import GaloisForLFunctions.RHTower.ThetaZeroDivisionRateTomography
import GaloisForLFunctions.HTGeometry.CompletelyMonotoneTower

/-!
# A single derivative witnesses all-sieve failure

For the perturbed source `f_ε = k + εu` of a zero division, the deleted fluxes `b_{D_S f_ε}` and the
cofinal flux `B_ε` are smooth on `t > 1`, and their derivatives differentiate under the rate
integral:
`b^{(k)}(t) = (1 + εc) φ_k(t) + ε ∫₀^∞ K(s) e^{5s/2} e^{2ks} φ_k(e^{2s} t) ds`,
with `φ_k(τ) = Σ_{(n,S)=1} 2π n² (−π n²)^k e^{−π n² τ}` for the deleted flux and
`φ_k(τ) = 2π(−π)^k e^{−πτ}` for `B_ε`.  These Gaussian-rate towers satisfy
`|φ_k(τ)| ≤ A e^{−πτ}` on `τ ≥ t₀ > 0` uniformly in the deleted primes, so along every exhaustion of
the primes every derivative of the deleted flux converges to that of `B_ε`.

`B_ε(1 + ·)` is not completely monotone; its derivative tower would otherwise alternate in sign
and make every forward difference alternate.  Hence one order `k` and one `t > 1` have
`(−1)^k B_ε^{(k)}(t) < 0`, and the same strict sign holds for all sufficiently deep deleted fluxes.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry (CompletelyMonotoneOn CompletelyMonotoneDiff CompletelyMonotoneTower
  fwdDiff_iterate_alternating)

namespace RHTower

noncomputable section

/-! ## Derivative towers -/

/-- Iterated derivatives agree with a derivative tower on an open set where the tower starts at
`f`. -/
theorem iteratedDeriv_eqOn_of_tower {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hF : ∀ k x, x ∈ U → HasDerivAt (F k) (F (k + 1) x) x) (hf : EqOn f (F 0) U) (k : ℕ) :
    EqOn (iteratedDeriv k f) (F k) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro x hx
    rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih),
      (hF k x hx).deriv]

/-- `e^{As} e^{-π e^{2s} t} ≤ e^{(A+1)²/(8πt)} e^{-s}` for `s ≥ 0`, `t > 0`. -/
theorem exp_mul_gaussRate_le (A : ℝ) {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    Real.exp (A * s) * Real.exp (-Real.pi * (Real.exp (2 * s) * t)) ≤
      Real.exp ((A + 1) ^ 2 / (8 * Real.pi * t)) * Real.exp (-s) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * s by linarith)
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have h8 : 0 < 8 * Real.pi * t := by positivity
  set c := (A + 1) ^ 2 / (8 * Real.pi * t)
  have hc : c * (8 * Real.pi * t) = (A + 1) ^ 2 := div_mul_cancel₀ _ h8.ne'
  have key : (A + 1) * s ≤ c + 2 * (Real.pi * t) * s ^ 2 := by
    nlinarith [sq_nonneg ((A + 1) - 4 * (Real.pi * t) * s)]
  have h1 : Real.pi * t * (1 + 2 * s + (2 * s) ^ 2 / 2) ≤ Real.pi * (Real.exp (2 * s) * t) := by
    nlinarith
  nlinarith

theorem integrableOn_exp_mul_gaussRate (A : ℝ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s => Real.exp (A * s) * Real.exp (-Real.pi * (Real.exp (2 * s) * t)))
      (Ioi 0) := by
  have hI : IntegrableOn (fun s : ℝ => Real.exp ((A + 1) ^ 2 / (8 * Real.pi * t)) * Real.exp (-s))
      (Ioi 0) :=
    IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul
      (Real.exp ((A + 1) ^ 2 / (8 * Real.pi * t)))) (fun s _ => by simp) measurableSet_Ioi
  refine Integrable.mono' hI (by fun_prop : Continuous _).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact exp_mul_gaussRate_le A ht (le_of_lt hs)

/-- A derivative tower on `(0,∞)` with Gaussian-rate decay: `φ_{k+1} = φ_k'` and
`|φ_k(τ)| ≤ A e^{-πτ}` for `τ ≥ t₀ > 0`. -/
structure GaussianRateTower (φ : ℕ → ℝ → ℝ) : Prop where
  hasDeriv : ∀ k τ, 0 < τ → HasDerivAt (φ k) (φ (k + 1) τ) τ
  bound : ∀ k (t₀ : ℝ), 0 < t₀ → ∃ A, 0 ≤ A ∧ ∀ τ, t₀ ≤ τ → |φ k τ| ≤ A * Real.exp (-Real.pi * τ)

/-- The flux tower `a φ_k(t) + ε ∫₀^∞ K(s) e^{5s/2} e^{2ks} φ_k(e^{2s} t) ds`. -/
def rateFluxTower (a ε : ℝ) (K : ℝ → ℝ) (φ : ℕ → ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  a * φ k t + ε * ∫ s in Ioi (0 : ℝ),
    K s * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k * φ k (Real.exp (2 * s) * t))

section Tower

variable {K : ℝ → ℝ} {C B : ℝ}

theorem rateFlux_integrand_le {ψ : ℝ → ℝ} {A t₀ : ℝ} (hA : 0 ≤ A)
    (hψ : ∀ τ, t₀ ≤ τ → |ψ τ| ≤ A * Real.exp (-Real.pi * τ)) (hC : 0 ≤ C)
    (hK : ∀ s, 0 ≤ s → |K s| ≤ C * Real.exp (B * s)) (k : ℕ) (ht₀ : 0 < t₀) {s x : ℝ}
    (hs : 0 ≤ s) (hx : t₀ ≤ x) :
    |K s * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k * ψ (Real.exp (2 * s) * x))| ≤
      C * A * (Real.exp ((B + 5 / 2 + 2 * k) * s) *
        Real.exp (-Real.pi * (Real.exp (2 * s) * t₀))) := by
  have he : 1 ≤ Real.exp (2 * s) := Real.one_le_exp (by linarith)
  have hτ : t₀ ≤ Real.exp (2 * s) * x := by nlinarith
  have h1 := hψ _ hτ
  have h2 : Real.exp (-Real.pi * (Real.exp (2 * s) * x)) ≤
      Real.exp (-Real.pi * (Real.exp (2 * s) * t₀)) :=
    Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_left hx (Real.exp_pos (2 * s)).le
      nlinarith [Real.pi_pos])
  have hexp : Real.exp ((B + 5 / 2 + 2 * k) * s) =
      Real.exp (B * s) * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (pow_pos (Real.exp_pos _) _),
    hexp]
  calc |K s| * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k * |ψ (Real.exp (2 * s) * x)|)
      ≤ (C * Real.exp (B * s)) * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k *
          (A * Real.exp (-Real.pi * (Real.exp (2 * s) * t₀)))) := by
        gcongr
        · exact hK s hs
        · exact h1.trans (mul_le_mul_of_nonneg_left h2 hA)
    _ = _ := by ring

theorem GaussianRateTower.continuous_integrand {φ : ℕ → ℝ → ℝ} (hφ : GaussianRateTower φ)
    (hKc : Continuous K) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Continuous fun s => K s * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k *
      φ k (Real.exp (2 * s) * x)) := by
  have hφc : Continuous fun s => φ k (Real.exp (2 * s) * x) :=
    continuous_iff_continuousAt.2 fun s =>
      (hφ.hasDeriv k _ (by positivity)).continuousAt.comp (f := fun s => Real.exp (2 * s) * x)
        (by fun_prop : Continuous fun s : ℝ => Real.exp (2 * s) * x).continuousAt
  exact hKc.mul ((by fun_prop : Continuous fun s : ℝ => Real.exp (5 * s / 2) *
    Real.exp (2 * s) ^ k).mul hφc)

theorem GaussianRateTower.integrableOn_integrand {φ : ℕ → ℝ → ℝ} (hφ : GaussianRateTower φ)
    (hKc : Continuous K) (hC : 0 ≤ C) (hK : ∀ s, 0 ≤ s → |K s| ≤ C * Real.exp (B * s)) (k : ℕ)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s => K s * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k *
      φ k (Real.exp (2 * s) * x))) (Ioi 0) := by
  obtain ⟨A, hA, hb⟩ := hφ.bound k x hx
  refine Integrable.mono' ((integrableOn_exp_mul_gaussRate (B + 5 / 2 + 2 * (k : ℝ)) hx).const_mul
    (C * A)) (hφ.continuous_integrand hKc k hx).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact rateFlux_integrand_le hA hb hC hK k hx (le_of_lt hs) le_rfl

/-- **Differentiation under the integral.** -/
theorem GaussianRateTower.hasDerivAt_rateFluxTower {φ : ℕ → ℝ → ℝ} (hφ : GaussianRateTower φ)
    (hKc : Continuous K) (hC : 0 ≤ C) (hK : ∀ s, 0 ≤ s → |K s| ≤ C * Real.exp (B * s))
    (a ε : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (rateFluxTower a ε K φ k) (rateFluxTower a ε K φ (k + 1) t) t := by
  set t₀ := t / 2 with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  obtain ⟨A, hA, hb⟩ := hφ.bound (k + 1) t₀ ht₀
  have hball : Ioi t₀ ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x s => K s * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k * φ k (Real.exp (2 * s) * x)))
    (F' := fun x s => K s * (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ (k + 1) *
      φ (k + 1) (Real.exp (2 * s) * x)))
    (bound := fun s => C * A * (Real.exp ((B + 5 / 2 + 2 * ((k + 1 : ℕ) : ℝ)) * s) *
      Real.exp (-Real.pi * (Real.exp (2 * s) * t₀))))
    (x₀ := t) hball ?_ (hφ.integrableOn_integrand hKc hC hK k ht)
    (hφ.continuous_integrand hKc (k + 1) ht).aestronglyMeasurable ?_
    ((integrableOn_exp_mul_gaussRate _ ht₀).const_mul (C * A)) ?_
  · unfold rateFluxTower
    exact ((hφ.hasDeriv k t ht).const_mul a).add (hmain.2.const_mul ε)
  · filter_upwards [hball] with x hx
    exact (hφ.continuous_integrand hKc k (ht₀.trans hx)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs x hx => ?_)
    rw [Real.norm_eq_abs]
    exact rateFlux_integrand_le hA hb hC hK (k + 1) ht₀ (le_of_lt hs) (le_of_lt hx)
  · refine Eventually.of_forall fun s x hx => ?_
    have hx0 : 0 < x := ht₀.trans hx
    have hd : HasDerivAt (fun x => φ k (Real.exp (2 * s) * x))
        (φ (k + 1) (Real.exp (2 * s) * x) * Real.exp (2 * s)) x := by
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (2 * s) * x) (Real.exp (2 * s)) x := by
        simpa using (hasDerivAt_id x).const_mul (Real.exp (2 * s))
      exact (hφ.hasDeriv k _ (by positivity)).comp x h1
    exact ((hd.const_mul (Real.exp (5 * s / 2) * Real.exp (2 * s) ^ k)).const_mul (K s)).congr_deriv
      (by ring)

/-- **Termwise convergence of flux towers** under a uniform Gaussian-rate bound. -/
theorem tendsto_rateFluxTower {φs : ℕ → ℕ → ℝ → ℝ} {φ : ℕ → ℝ → ℝ}
    (hφs : ∀ j, GaussianRateTower (φs j))
    (hunif : ∀ k (t₀ : ℝ), 0 < t₀ → ∃ A, 0 ≤ A ∧ ∀ j τ, t₀ ≤ τ →
      |φs j k τ| ≤ A * Real.exp (-Real.pi * τ))
    (hlim : ∀ k τ, 0 < τ → Tendsto (fun j => φs j k τ) atTop (𝓝 (φ k τ)))
    (hKc : Continuous K) (hC : 0 ≤ C) (hK : ∀ s, 0 ≤ s → |K s| ≤ C * Real.exp (B * s))
    (a ε : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => rateFluxTower a ε K (φs j) k t) atTop (𝓝 (rateFluxTower a ε K φ k t)) := by
  obtain ⟨A, hA, hb⟩ := hunif k t ht
  unfold rateFluxTower
  refine ((hlim k t ht).const_mul a).add (Tendsto.const_mul ε ?_)
  refine tendsto_integral_of_dominated_convergence (fun s => C * A *
      (Real.exp ((B + 5 / 2 + 2 * (k : ℝ)) * s) * Real.exp (-Real.pi * (Real.exp (2 * s) * t))))
    (fun j => ((hφs j).continuous_integrand hKc k ht).aestronglyMeasurable)
    ((integrableOn_exp_mul_gaussRate _ ht).const_mul (C * A)) (fun j => ?_) ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    exact rateFlux_integrand_le hA (hb j) hC hK k ht (le_of_lt hs) le_rfl
  · refine Eventually.of_forall fun s => ?_
    exact ((hlim k _ (by positivity)).const_mul _).const_mul _

end Tower

/-! ## The seed tower and the deleted towers -/

/-- The seed tower `2π(−π)^k e^{−πτ}`: the derivatives of the surviving atom `2π e^{−πτ}`. -/
def seedRateTower (k : ℕ) (τ : ℝ) : ℝ := 2 * Real.pi * (-Real.pi) ^ k * Real.exp (-Real.pi * τ)

theorem gaussianRateTower_seed : GaussianRateTower seedRateTower where
  hasDeriv k τ _ := by
    have h := (((hasDerivAt_id' τ).const_mul (-Real.pi)).exp).const_mul
      (2 * Real.pi * (-Real.pi) ^ k)
    exact h.congr_deriv (by unfold seedRateTower; ring)
  bound k t₀ _ := ⟨2 * Real.pi * Real.pi ^ k, by positivity, fun τ _ => by
    have : |seedRateTower k τ| = 2 * Real.pi * Real.pi ^ k * Real.exp (-Real.pi * τ) := by
      simp only [seedRateTower, abs_mul, abs_pow, abs_neg, abs_two, abs_of_pos Real.pi_pos,
        abs_of_pos (Real.exp_pos _)]
    exact this.le⟩

/-- The `k`-th derivative of the deleted theta flux atom `2π m² e^{−π m² τ}`. -/
def deletedAtom (k m : ℕ) (τ : ℝ) : ℝ :=
  2 * Real.pi * (m : ℝ) ^ 2 * (-Real.pi * (m : ℝ) ^ 2) ^ k * Real.exp (-Real.pi * (m : ℝ) ^ 2 * τ)

/-- The deleted tower `Σ_{(n, S) = 1} 2π n² (−π n²)^k e^{−π n² τ}`. -/
def deletedRateTower (S : Finset ℕ) (k : ℕ) (τ : ℝ) : ℝ :=
  ∑' n : ℕ, (thetaCoprimeLabels S).indicator (fun m => deletedAtom k m τ) n

theorem abs_deletedAtom (k m : ℕ) (τ : ℝ) :
    |deletedAtom k m τ| =
      2 * Real.pi * Real.pi ^ k * ((m : ℝ) ^ (2 * k + 2) * Real.exp (-(Real.pi * τ) * (m : ℝ) ^ 2)) := by
  have h1 : |(-Real.pi * (m : ℝ) ^ 2) ^ k| = (Real.pi * (m : ℝ) ^ 2) ^ k := by
    rw [abs_pow, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_of_nonneg (sq_nonneg _)]
  rw [deletedAtom, abs_mul, abs_mul, h1, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (m : ℝ) ^ 2),
    abs_of_pos (Real.exp_pos _), show -(Real.pi * τ) * (m : ℝ) ^ 2 = -Real.pi * (m : ℝ) ^ 2 * τ by ring]
  ring

theorem summable_abs_deletedAtom (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable fun m : ℕ =>
      2 * Real.pi * Real.pi ^ k * ((m : ℝ) ^ (2 * k + 2) * Real.exp (-(Real.pi * τ) * (m : ℝ) ^ 2)) :=
  (summable_pow_mul_exp_neg_nat_sq (2 * k + 2) (by positivity)).mul_left _

theorem abs_indicator_deletedAtom_le (S : Finset ℕ) (k m : ℕ) (τ : ℝ) :
    |(thetaCoprimeLabels S).indicator (fun m => deletedAtom k m τ) m| ≤ |deletedAtom k m τ| := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

theorem summable_deletedAtom (S : Finset ℕ) (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable fun m : ℕ => |(thetaCoprimeLabels S).indicator (fun m => deletedAtom k m τ) m| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun m => (abs_indicator_deletedAtom_le S k m τ).trans (abs_deletedAtom k m τ).le)
    (summable_abs_deletedAtom k hτ)

/-- The constant `e^{π t₀} Σ_m 2π π^k m^{2k+2} e^{−π t₀ m²}`, uniform in the deleted primes. -/
def deletedTowerConst (k : ℕ) (t₀ : ℝ) : ℝ :=
  Real.exp (Real.pi * t₀) * ∑' m : ℕ,
    2 * Real.pi * Real.pi ^ k * ((m : ℝ) ^ (2 * k + 2) * Real.exp (-(Real.pi * t₀) * (m : ℝ) ^ 2))

theorem deletedTowerConst_nonneg (k : ℕ) (t₀ : ℝ) : 0 ≤ deletedTowerConst k t₀ :=
  mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun m => by positivity)

/-- **Uniform Gaussian-rate bound** for every deleted tower. -/
theorem abs_deletedRateTower_le (S : Finset ℕ) (k : ℕ) {t₀ τ : ℝ} (ht₀ : 0 < t₀) (hτ : t₀ ≤ τ) :
    |deletedRateTower S k τ| ≤ deletedTowerConst k t₀ * Real.exp (-Real.pi * τ) := by
  have hsum := summable_deletedAtom S k (ht₀.trans_le hτ)
  have hnorm : |deletedRateTower S k τ| ≤
      ∑' m : ℕ, |(thetaCoprimeLabels S).indicator (fun m => deletedAtom k m τ) m| := by
    have := norm_tsum_le_tsum_norm (f := fun m : ℕ =>
      (thetaCoprimeLabels S).indicator (fun m => deletedAtom k m τ) m) (by simpa using hsum)
    simpa [deletedRateTower] using this
  refine hnorm.trans ?_
  rw [deletedTowerConst, mul_comm (Real.exp (Real.pi * t₀)), mul_assoc, ← tsum_mul_right]
  refine hsum.tsum_le_tsum (fun m => ?_) ((summable_abs_deletedAtom k ht₀).mul_right _)
  refine (abs_indicator_deletedAtom_le S k m τ).trans ?_
  rw [abs_deletedAtom]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have hexp : Real.exp (-(Real.pi * τ) * (m : ℝ) ^ 2) ≤ Real.exp (-(Real.pi * t₀) * (m : ℝ) ^ 2) *
        (Real.exp (Real.pi * t₀) * Real.exp (-Real.pi * τ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      have hprod := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hm1)) (sub_nonneg.2 hτ)
      exact Real.exp_le_exp.2 (by nlinarith [hprod])
    calc 2 * Real.pi * Real.pi ^ k * ((m : ℝ) ^ (2 * k + 2) * Real.exp (-(Real.pi * τ) * (m : ℝ) ^ 2))
        ≤ 2 * Real.pi * Real.pi ^ k * ((m : ℝ) ^ (2 * k + 2) * (Real.exp (-(Real.pi * t₀) * (m : ℝ) ^ 2) *
            (Real.exp (Real.pi * t₀) * Real.exp (-Real.pi * τ)))) := by gcongr
      _ = _ := by ring

theorem gaussianRateTower_deleted (S : Finset ℕ) : GaussianRateTower (deletedRateTower S) where
  hasDeriv k τ hτ := by
    have hmem : τ ∈ Ioi (τ / 2) := by simp only [mem_Ioi]; linarith
    refine hasDerivAt_tsum_of_isPreconnected
      (g := fun n y => (thetaCoprimeLabels S).indicator (fun m => deletedAtom k m y) n)
      (g' := fun n y => (thetaCoprimeLabels S).indicator (fun m => deletedAtom (k + 1) m y) n)
      (summable_abs_deletedAtom (k + 1) (half_pos hτ))
      isOpen_Ioi isPreconnected_Ioi (fun n y _ => ?_) (fun n y hy => ?_) hmem
      (summable_deletedAtom S k hτ).of_abs hmem
    · by_cases hn : n ∈ thetaCoprimeLabels S
      · simp only [Set.indicator_of_mem hn]
        have := (((hasDerivAt_id' y).const_mul (-Real.pi * (n : ℝ) ^ 2)).exp).const_mul
          (2 * Real.pi * (n : ℝ) ^ 2 * (-Real.pi * (n : ℝ) ^ 2) ^ k)
        exact this.congr_deriv (by unfold deletedAtom; ring)
      · simp only [Set.indicator_of_notMem hn]
        exact hasDerivAt_const _ _
    · rw [Real.norm_eq_abs]
      refine (abs_indicator_deletedAtom_le S (k + 1) n y).trans ?_
      rw [abs_deletedAtom]
      have hy' : τ / 2 < y := hy
      gcongr
  bound k t₀ ht₀ := ⟨deletedTowerConst k t₀, deletedTowerConst_nonneg k t₀,
    fun τ hτ => abs_deletedRateTower_le S k ht₀ hτ⟩

/-- **Cofinal limit of the deleted towers**: only the atom `n = 1` survives. -/
theorem tendsto_deletedRateTower {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) (k : ℕ) {τ : ℝ}
    (hτ : 0 < τ) :
    Tendsto (fun j => deletedRateTower (S j) k τ) atTop (𝓝 (seedRateTower k τ)) := by
  classical
  have hlim : seedRateTower k τ = ∑' n : ℕ, if n = 1 then deletedAtom k n τ else 0 := by
    rw [tsum_eq_single 1 (fun n hn => if_neg hn), if_pos rfl]
    simp [seedRateTower, deletedAtom]
  rw [hlim]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => |deletedAtom k m τ|)
    ((summable_abs_deletedAtom k hτ).congr fun m => (abs_deletedAtom k m τ).symm)
    (fun n => ?_) (Eventually.of_forall fun j n => ?_)
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have h0 : ∀ j, (thetaCoprimeLabels (S j)).indicator (fun m => deletedAtom k m τ) 0 = 0 :=
          fun j => by rw [Set.indicator_apply]; split_ifs <;> simp [deletedAtom]
        simp only [h0, show (0 : ℕ) ≠ 1 by norm_num, if_false]
        exact tendsto_const_nhds
      · have h1 : ∀ j, (1 : ℕ) ∈ thetaCoprimeLabels (S j) := fun j p hp hdiv =>
          (hS.prime j p hp).one_lt.ne' (Nat.dvd_one.mp hdiv)
        simp only [Set.indicator_of_mem (h1 _), if_true]
        exact tendsto_const_nhds
    · rw [if_neg (by omega)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hS.eventually_not_coprime hn] with j hj
      rw [Set.indicator_of_notMem (show n ∉ thetaCoprimeLabels (S j) from hj)]
  · rw [Real.norm_eq_abs]
    exact abs_indicator_deletedAtom_le (S j) k n τ

theorem deletedRateTower_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {u : ℝ} (hu : 0 < u) :
    deletedRateTower S 0 u = thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) u := by
  rw [thetaNormalizedFlux_thetaPrimeDeletion_eq hS hu]
  simp [deletedRateTower, deletedAtom]

/-! ## Derivatives of the deleted fluxes and of the cofinal flux -/

theorem rateFluxTower_deleted_zero (L : List ℂ) (N : Polynomial ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ε : ℝ) {t : ℝ} (ht : 1 < t) :
    rateFluxTower (1 + ε * causalRateConst L N) ε (causalRateKernel L N) (deletedRateTower S) 0 t =
      thetaNormalizedFlux (thetaPrimeDeletion S (perturbedSource L N ε)) t := by
  rw [thetaNormalizedFlux_perturbedSource L N hS ε ht]
  unfold rateFluxTower
  rw [deletedRateTower_zero hS (by linarith)]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [deletedRateTower_zero hS (by positivity), pow_zero, mul_one]

theorem rateFluxTower_seed_zero (L : List ℂ) (N : Polynomial ℝ) (ε t : ℝ) :
    rateFluxTower (1 + ε * causalRateConst L N) ε (causalRateKernel L N) seedRateTower 0 t =
      cofinalFlux L N ε t := by
  unfold rateFluxTower cofinalFlux seedRateTower
  simp only [pow_zero, mul_one]

/-- The derivatives of `B_ε` differentiate under the rate integral. -/
theorem iteratedDeriv_cofinalFlux (L : List ℂ) (N : Polynomial ℝ) (ε : ℝ) (k : ℕ) {t : ℝ}
    (ht : 0 < t) :
    iteratedDeriv k (cofinalFlux L N ε) t =
      rateFluxTower (1 + ε * causalRateConst L N) ε (causalRateKernel L N) seedRateTower k t := by
  obtain ⟨C, B, hC, -, hK⟩ := exists_abs_causalRateKernel_le L N
  exact iteratedDeriv_eqOn_of_tower isOpen_Ioi (fun k x hx =>
    gaussianRateTower_seed.hasDerivAt_rateFluxTower (continuous_causalRateKernel L N) hC hK _ _ k hx)
    (fun x _ => (rateFluxTower_seed_zero L N ε x).symm) k ht

/-- **Differentiated deleted flux.**  For `t > 1` the derivatives of `b_{D_S f_ε}` differentiate the
deleted-flux formula under the rate integral. -/
theorem iteratedDeriv_flux_perturbedSource (L : List ℂ) (N : Polynomial ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ε : ℝ) (k : ℕ) {t : ℝ} (ht : 1 < t) :
    iteratedDeriv k (thetaNormalizedFlux (thetaPrimeDeletion S (perturbedSource L N ε))) t =
      rateFluxTower (1 + ε * causalRateConst L N) ε (causalRateKernel L N) (deletedRateTower S) k t := by
  obtain ⟨C, B, hC, -, hK⟩ := exists_abs_causalRateKernel_le L N
  exact iteratedDeriv_eqOn_of_tower (U := Ioi 1) isOpen_Ioi (fun k x hx =>
    (gaussianRateTower_deleted S).hasDerivAt_rateFluxTower (continuous_causalRateKernel L N) hC hK
      _ _ k (zero_lt_one.trans hx))
    (fun x hx => (rateFluxTower_deleted_zero L N hS ε hx).symm) k ht

/-- **Derivative convergence under cofinal deletion.** -/
theorem tendsto_iteratedDeriv_flux_perturbedSource (L : List ℂ) (N : Polynomial ℝ)
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) (ε : ℝ) (k : ℕ) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun j => iteratedDeriv k
        (thetaNormalizedFlux (thetaPrimeDeletion (S j) (perturbedSource L N ε))) t) atTop
      (𝓝 (iteratedDeriv k (cofinalFlux L N ε) t)) := by
  obtain ⟨C, B, hC, -, hK⟩ := exists_abs_causalRateKernel_le L N
  rw [iteratedDeriv_cofinalFlux L N ε k (by linarith)]
  simp_rw [fun j => iteratedDeriv_flux_perturbedSource L N (hS.prime j) ε k ht]
  exact tendsto_rateFluxTower (fun j => gaussianRateTower_deleted (S j))
    (fun k t₀ ht₀ => ⟨deletedTowerConst k t₀, deletedTowerConst_nonneg k t₀,
      fun j τ hτ => abs_deletedRateTower_le (S j) k ht₀ hτ⟩)
    (fun k τ hτ => tendsto_deletedRateTower hS k hτ) (continuous_causalRateKernel L N) hC hK _ _ k
    (by linarith)

section Witness

variable {L : List ℂ} (hL : ThetaDivisionList L) (hconj : (L.map (starRingEnd ℂ)).Perm L)
  {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length) (hN0 : N.eval 0 = 0) (hNne : N ≠ 0)
include hL hconj hN hN0 hNne

/-- **A derivative sign of `B_ε` fails.**  Otherwise `u ↦ B_ε(1 + u)` with its derivative tower is
completely monotone, which it is not. -/
theorem exists_iteratedDeriv_cofinalFlux_neg {ε : ℝ} (hε : ε ≠ 0) :
    ∃ (k : ℕ) (t : ℝ), 1 < t ∧ (-1 : ℝ) ^ k * iteratedDeriv k (cofinalFlux L N ε) t < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨C, B, hC, -, hK⟩ := exists_abs_causalRateKernel_le L N
  set F := rateFluxTower (1 + ε * causalRateConst L N) ε (causalRateKernel L N) seedRateTower
  have hFd : ∀ k x, 0 < x → HasDerivAt (F k) (F (k + 1) x) x := fun k x hx =>
    gaussianRateTower_seed.hasDerivAt_rateFluxTower (continuous_causalRateKernel L N) hC hK _ _ k hx
  have hT : CompletelyMonotoneTower (fun k u => F k (1 + u)) := by
    refine ⟨fun k x hx => ?_, fun k x hx => ?_⟩
    · have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      exact ((hFd k (1 + x) (by linarith)).comp x h1).congr_deriv (mul_one _)
    · have := hcon k (1 + x) (by linarith)
      rwa [iteratedDeriv_cofinalFlux L N ε k (by linarith)] at this
  have hT0 : (fun u => F 0 (1 + u)) = fun u => cofinalFlux L N ε (1 + u) :=
    funext fun u => rateFluxTower_seed_zero L N ε (1 + u)
  refine not_completelyMonotoneOn_cofinalFlux hL hconj hN hN0 hNne hε ⟨fun k δ hδ t ht => ?_, ?_⟩
  · have := fwdDiff_iterate_alternating hδ k hT ht
    rwa [hT0] at this
  · intro u hu
    have := (hT.hasDeriv 0 u hu).continuousAt.continuousWithinAt (s := Ioi 0)
    rwa [hT0] at this

/-- **Eventual finite-depth derivative witness.**  Along every exhaustion of the primes, one
derivative order `k` and one point `t > 1` witness the failure of complete monotonicity of every
sufficiently deep deleted flux of `f_ε = k + εu`: `(−1)^k b^{(k)}(t) < 0`. -/
theorem exists_allSieve_derivative_witness {ε : ℝ} (hε : ε ≠ 0) {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) :
    ∃ (k : ℕ) (t : ℝ), 1 < t ∧ ∀ᶠ j in atTop, (-1 : ℝ) ^ k * iteratedDeriv k
      (thetaNormalizedFlux (thetaPrimeDeletion (S j) (perturbedSource L N ε))) t < 0 := by
  obtain ⟨k, t, ht, hneg⟩ := exists_iteratedDeriv_cofinalFlux_neg hL hconj hN hN0 hNne hε
  refine ⟨k, t, ht, ?_⟩
  exact ((tendsto_iteratedDeriv_flux_perturbedSource L N hS ε k ht).const_mul ((-1 : ℝ) ^ k)).eventually
    (gt_mem_nhds hneg)

end Witness

end

end RHTower
