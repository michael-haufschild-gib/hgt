import GaloisForLFunctions.HTGeometry.DbarPolydiscSolve
import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass

/-!
# Holomorphy from the vanishing of `∂̄` on a set

The Cauchy–Riemann criterion is pointwise: at a point where every antiholomorphic partial derivative
of a real-differentiable function vanishes, the real differential commutes with multiplication by
`i`, hence is complex linear, hence the function is complex differentiable there.  So a
real-differentiable function whose `∂̄` vanishes on a set is holomorphic on that set.

* `HTGeometry.differentiableAt_complex_of_dzbarAt_eq_zero` : the pointwise criterion.
* `HTGeometry.differentiableOn_complex_of_dzbarAt_eq_zero` : the criterion on a set.
-/

namespace HTGeometry

open Complex

section PointwiseCauchyRiemann

variable {n : ℕ} {F : (Fin n → ℂ) → ℂ}

/-- **The vanishing of the `j`-th `∂̄` at a point** makes the differential there commute with `i` in
the `j`-th direction. -/
theorem map_I_single_at (hF : Differentiable ℝ F) {z : Fin n → ℂ}
    (hbar : ∀ j : Fin n, dzbarAt F j z = 0) (j : Fin n) (v : ℂ) :
    (fderiv ℝ F z) (Pi.single j (Complex.I * v))
      = Complex.I * (fderiv ℝ F z) (Pi.single j v) := by
  have hslice := hasFDerivAt_dbarSlice hF j z
  have hz : dzbar (dbarSlice F j z) (z j) = 0 := hbar j
  rw [dzbar_eq_of_hasFDerivAt hslice] at hz
  have hlin := (wirtingerAntihol_eq_zero_iff _).1 hz
  have h1 := hlin (Complex.I * v)
  have h2 := hlin v
  have hsingle : ∀ w : ℂ, ((fderiv ℝ F z).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) w
      = (fderiv ℝ F z) (Pi.single j w) := fun w => rfl
  rw [hsingle] at h1 h2
  rw [h1, h2]
  ring

/-- **The Cauchy–Riemann equations at a point.** -/
theorem map_I_at (hF : Differentiable ℝ F) {z : Fin n → ℂ}
    (hbar : ∀ j : Fin n, dzbarAt F j z = 0) (v : Fin n → ℂ) :
    (fderiv ℝ F z) (Complex.I • v) = Complex.I * (fderiv ℝ F z) v := by
  have hv : v = ∑ j : Fin n, Pi.single j (v j) := by
    funext i
    simp
  have hIv : (Complex.I • v) = ∑ j : Fin n, Pi.single j (Complex.I * v j) := by
    funext i
    simp
  calc (fderiv ℝ F z) (Complex.I • v)
      = ∑ j : Fin n, (fderiv ℝ F z) (Pi.single j (Complex.I * v j)) := by
        rw [hIv, map_sum]
    _ = ∑ j : Fin n, Complex.I * (fderiv ℝ F z) (Pi.single j (v j)) :=
        Finset.sum_congr rfl fun j _ => map_I_single_at hF hbar j (v j)
    _ = Complex.I * ∑ j : Fin n, (fderiv ℝ F z) (Pi.single j (v j)) := by
        rw [Finset.mul_sum]
    _ = Complex.I * (fderiv ℝ F z) v := by
        rw [← map_sum]
        congr 2
        exact hv.symm

/-- **`∂̄F = 0` at a point makes `F` complex differentiable there.** -/
theorem differentiableAt_complex_of_dzbarAt_eq_zero (hF : Differentiable ℝ F) {z : Fin n → ℂ}
    (hbar : ∀ j : Fin n, dzbarAt F j z = 0) : DifferentiableAt ℂ F z := by
  refine ⟨{ toFun := fderiv ℝ F z
            map_add' := (fderiv ℝ F z).map_add
            map_smul' := fun c x => map_smul_of_map_I (fderiv ℝ F z)
              (fun x => map_I_at hF hbar x) c x
            cont := (fderiv ℝ F z).continuous }, ?_⟩
  have h := (hF z).hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO] at h ⊢
  exact h

/-- **`∂̄F = 0` on a set makes `F` holomorphic there.** -/
theorem differentiableOn_complex_of_dzbarAt_eq_zero (hF : Differentiable ℝ F)
    {U : Set (Fin n → ℂ)} (hbar : ∀ (j : Fin n), ∀ z ∈ U, dzbarAt F j z = 0) :
    DifferentiableOn ℂ F U := fun z hz =>
  (differentiableAt_complex_of_dzbarAt_eq_zero hF fun j => hbar j z hz).differentiableWithinAt

end PointwiseCauchyRiemann

section HolomorphicDbar

variable {n : ℕ}

/-- The `∂̄` of a holomorphic function vanishes: its slices are holomorphic in one variable. -/
theorem dzbarAt_eq_zero_of_differentiable {F : (Fin n → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (j : Fin n) (z : Fin n → ℂ) : dzbarAt F j z = 0 := by
  have hemb : Differentiable ℂ (fun s : ℂ => (Function.update z j s : Fin n → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    by_cases h : i = j
    · subst h
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne h]
      exact differentiable_const _
  rw [dzbarAt]
  exact (dzbar_eq_zero_of_differentiableAt
    ((hF (Function.update z j (z j))).comp (z j) (hemb (z j)))).1

end HolomorphicDbar

section ApproxSequence

variable {n : ℕ}

open GaloisForLFunctions.HTGeometry

/-- The polydisc of the Dolbeault layer and the polydisc of the Cauchy layer agree. -/
theorem polydisc_eq_polydiscSet (c : Fin n → ℂ) (r : Fin n → ℝ) :
    polydisc c r = GaloisForLFunctions.HTGeometry.polydiscSet c r := rfl

/-- **The corrected sequence of local solutions of the `∂̄` system on `ℂⁿ`.**  The `m`-th member
solves the system on the ball of radius `m + 1`; consecutive members differ by a function
holomorphic there, corrected by an entire function so that the difference is at most `2^{-m}` on the
ball of radius `m`. -/
theorem exists_dbar_approx_sequence {f : Fin n → (Fin n → ℂ) → ℂ}
    (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ (j j' : Fin n) (z : Fin n → ℂ), dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ v : ℕ → (Fin n → ℂ) → ℂ,
      (∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v m)) ∧
      (∀ (m : ℕ) (j : Fin n), ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ((m : ℝ) + 1),
        dzbarAt (v m) j z = f j z) ∧
      (∀ m : ℕ, DifferentiableOn ℂ (fun z => v (m + 1) z - v m z)
        (Metric.ball (0 : Fin n → ℂ) ((m : ℝ) + 1))) ∧
      (∀ m : ℕ, ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) (m : ℝ),
        ‖v (m + 1) z - v m z‖ ≤ (1 / 2) ^ m) := by
  classical
  -- local solutions
  have hstep : ∀ m : ℕ, ∃ w : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w ∧
      ∀ j : Fin n, ∀ z ∈ polydisc (0 : Fin n → ℂ) (fun _ => (m : ℝ) + 1),
        dzbarAt w j z = f j z := by
    intro m
    exact dbar_polydisc_solve (c := 0) (r := fun _ => (m : ℝ) + 2)
      (ρ := fun _ => (m : ℝ) + 1) (fun _ => by positivity) (fun _ => by linarith) hCf
      (fun j j' z _ => hclosed j j' z)
  choose u hCu hu using hstep
  have hball : ∀ m : ℕ, polydisc (0 : Fin n → ℂ) (fun _ => (m : ℝ) + 1)
      = Metric.ball (0 : Fin n → ℂ) ((m : ℝ) + 1) := by
    intro m
    rw [polydisc_eq_polydiscSet]
    exact polydiscSet_const 0 (by positivity)
  have hdu : ∀ m : ℕ, Differentiable ℝ (fun z => u (m + 1) z - u m z) := fun m =>
    ((hCu (m + 1)).differentiable (by simp)).sub ((hCu m).differentiable (by simp))
  have hdiffdu : ∀ m : ℕ, DifferentiableOn ℂ (fun z => u (m + 1) z - u m z)
      (Metric.ball (0 : Fin n → ℂ) ((m : ℝ) + 1)) := by
    intro m
    refine differentiableOn_complex_of_dzbarAt_eq_zero (hdu m) ?_
    intro j z hz
    rw [dzbarAt_sub ((hCu (m + 1)).differentiable (by simp))
      ((hCu m).differentiable (by simp)) j z]
    have h1 : dzbarAt (u (m + 1)) j z = f j z := by
      refine hu (m + 1) j z ?_
      rw [hball (m + 1)]
      refine Metric.ball_subset_ball ?_ hz
      push_cast
      linarith
    have h2 : dzbarAt (u m) j z = f j z := by
      refine hu m j z ?_
      rw [hball m]
      exact hz
    rw [h1, h2, sub_self]
  -- entire approximations of the consecutive differences
  have happrox : ∀ m : ℕ, ∃ P : (Fin n → ℂ) → ℂ, Differentiable ℂ P ∧
      ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) (m : ℝ),
        ‖(u (m + 1) z - u m z) - P z‖ ≤ (1 / 2) ^ m := by
    intro m
    refine exists_entire_approx_closedBall (f := fun z => u (m + 1) z - u m z)
      0 (R := (m : ℝ) + 1 / 2)
      (R₁ := (m : ℝ) + 1) (ρ := (m : ℝ)) (ε := (1 / 2) ^ m) (by positivity) (by linarith) ?_
      (by positivity) (by linarith) (by positivity)
    rw [polydiscSet_const 0 (by positivity)]
    exact hdiffdu m
  choose P hPdiff hPapprox using happrox
  have hPsmooth : ∀ l : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P l) := by
    intro l
    have hC : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (P l) :=
      (contDiff_of_continuous_affineLineEntire (hPdiff l).continuous
        (affineLineEntire_of_differentiable (hPdiff l))).of_le le_top
    exact hC.restrict_scalars ℝ
  have hSC : ∀ m : ℕ, Differentiable ℂ
      (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w) := by
    intro m
    have heq : (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w)
        = ∑ l ∈ Finset.range m, P l := by
      funext w
      simp
    rw [heq]
    exact Differentiable.sum fun l _ => hPdiff l
  have hSsmooth : ∀ m : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w) :=
    fun m => ContDiff.sum fun l _ => hPsmooth l
  have hdiffstep : ∀ m : ℕ, (fun z : Fin n → ℂ =>
      (u (m + 1) z - ∑ l ∈ Finset.range (m + 1), P l z) -
        (u m z - ∑ l ∈ Finset.range m, P l z))
      = fun z : Fin n → ℂ => (u (m + 1) z - u m z) - P m z := by
    intro m
    funext z
    rw [Finset.sum_range_succ]
    ring
  refine ⟨fun m z => u m z - ∑ l ∈ Finset.range m, P l z, fun m => (hCu m).sub (hSsmooth m),
    ?_, ?_, ?_⟩
  · intro m j z hz
    show dzbarAt (fun w => u m w - ∑ l ∈ Finset.range m, P l w) j z = f j z
    rw [dzbarAt_sub ((hCu m).differentiable (by simp))
      ((hSC m).restrictScalars ℝ) j z,
      dzbarAt_eq_zero_of_differentiable (hSC m) j z,
      hu m j z (by rw [hball m]; exact hz), sub_zero]
  · intro m
    rw [hdiffstep m]
    exact (hdiffdu m).sub ((hPdiff m).differentiableOn)
  · intro m z hz
    have h := congrFun (hdiffstep m) z
    rw [h]
    exact hPapprox m z hz

end ApproxSequence

section MittagLeffler

variable {n : ℕ}

open GaloisForLFunctions.HTGeometry

/-- Prepending a variable coordinate to a fixed point is holomorphic. -/
theorem differentiable_updateEmbed_complex (j : Fin n) (z : Fin n → ℂ) :
    Differentiable ℂ (fun s : ℂ => (Function.update z j s : Fin n → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  by_cases h : i = j
  · subst h
    simp only [Function.update_self]
    exact differentiable_id
  · simp only [Function.update_of_ne h]
    exact differentiable_const _

/-- **`∂̄_j` of a function holomorphic on an open set vanishes there.** -/
theorem dzbarAt_eq_zero_of_differentiableOn {F : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {z : Fin n → ℂ} (hz : z ∈ U) (j : Fin n) :
    dzbarAt F j z = 0 := by
  have hFz : DifferentiableAt ℂ F z := hF.differentiableAt (hU.mem_nhds hz)
  have hupd : Function.update z j (z j) = z := Function.update_eq_self j z
  have hcomp : DifferentiableAt ℂ (fun t : ℂ => F (Function.update z j t)) (z j) := by
    refine DifferentiableAt.comp (z j) ?_ ((differentiable_updateEmbed_complex j z) (z j))
    rw [hupd]
    exact hFz
  rw [dzbarAt]
  exact (dzbar_eq_zero_of_differentiableAt hcomp).1

/-- **Holomorphy on an open set gives smoothness there**, for a globally continuous function. -/
theorem contDiffAt_of_differentiableOn {F : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {z : Fin n → ℂ}
    (hz : z ∈ U) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z := by
  obtain ⟨R₁, hR₁pos, hR₁sub⟩ := Metric.isOpen_iff.1 hU z hz
  have hdiff : DifferentiableOn ℂ F (polydiscSet z fun _ => R₁) := by
    rw [polydiscSet_const z hR₁pos]
    exact hF.mono hR₁sub
  have hball := polydiscHasFPowerSeriesOnBall_of_differentiableOn z
    (R := R₁ / 2) (R₁ := R₁) (by positivity) (by linarith) hdiff
  exact (hball.analyticAt.contDiffAt (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ

/-- **Global solvability of the `∂̄` system on `ℂⁿ`.**  A smooth `∂̄`-closed datum on the whole space
has a smooth primitive on the whole space.  The local solutions of the Dolbeault–Grothendieck lemma
on the balls of integer radius are corrected by entire functions, chosen by the Runge step so that
consecutive corrected solutions differ by at most `2^{-m}` on the ball of radius `m`; the corrected
sequence converges uniformly on every ball, its limit differs from each member by a locally uniform
limit of holomorphic functions, and Weierstrass' theorem makes that difference holomorphic, so the
limit solves the system wherever the member does. -/
theorem dbar_global_solve {f : Fin n → (Fin n → ℂ) → ℂ}
    (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ (j j' : Fin n) (z : Fin n → ℂ), dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      ∀ (j : Fin n) (z : Fin n → ℂ), dzbarAt u j z = f j z := by
  classical
  obtain ⟨v, hCv, hsolve, hholo, hest⟩ := exists_dbar_approx_sequence hCf hclosed
  set D : ℕ → (Fin n → ℂ) → ℂ := fun m z => v (m + 1) z - v m z with hD
  have hDest : ∀ (m : ℕ) (z : Fin n → ℂ), ‖z‖ ≤ (m : ℝ) → ‖D m z‖ ≤ (1 / 2 : ℝ) ^ m := by
    intro m z hz
    exact hest m z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
  have hDsummable : ∀ z : Fin n → ℂ, Summable fun m => D m z := by
    intro z
    refine Summable.of_norm_bounded_eventually summable_geometric_two ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with m hm
    exact hDest m z (le_trans (Nat.le_ceil ‖z‖) (by exact_mod_cast hm))
  set w : (Fin n → ℂ) → ℂ := fun z => v 0 z + ∑' m, D m z with hw
  have htele : ∀ (N : ℕ) (z : Fin n → ℂ), w z - v N z = ∑' m, D (m + N) z := by
    intro N z
    have h1 : ∑ i ∈ Finset.range N, D i z = v N z - v 0 z :=
      Finset.sum_range_sub (fun k => v k z) N
    have h2 := (hDsummable z).sum_add_tsum_nat_add N
    show v 0 z + ∑' m, D m z - v N z = _
    rw [← h2, h1]
    ring
  have htail : ∀ (N : ℕ) (z : Fin n → ℂ), ‖z‖ ≤ (N : ℝ) →
      ‖w z - v N z‖ ≤ 2 * (1 / 2 : ℝ) ^ N := by
    intro N z hz
    have hb : ∀ m : ℕ, ‖D (m + N) z‖ ≤ (1 / 2 : ℝ) ^ (m + N) := by
      intro m
      refine hDest (m + N) z (le_trans hz ?_)
      exact_mod_cast Nat.le_add_left N m
    have hsg : Summable fun m : ℕ => (1 / 2 : ℝ) ^ (m + N) := by
      simpa [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ N)
    have hns : Summable fun m : ℕ => ‖D (m + N) z‖ :=
      hsg.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    rw [htele N z]
    refine le_trans (norm_tsum_le_tsum_norm hns) ?_
    refine le_trans (Summable.tsum_le_tsum hb hns hsg) ?_
    have : ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + N) = 2 * (1 / 2 : ℝ) ^ N := by
      simp only [pow_add]
      rw [tsum_mul_right, tsum_geometric_two]
    exact le_of_eq this
  have hunif : ∀ M : ℕ, TendstoUniformlyOn (fun (N : ℕ) (z : Fin n → ℂ) => v N z) w
      Filter.atTop (Metric.closedBall (0 : Fin n → ℂ) (M : ℝ)) := by
    intro M
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hzero : Filter.Tendsto (fun N : ℕ => 2 * (1 / 2 : ℝ) ^ N) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      simpa using this.const_mul 2
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hzero) ε hε
    filter_upwards [Filter.eventually_ge_atTop (max N₀ M)] with N hN z hz
    have hzN : ‖z‖ ≤ (N : ℝ) := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      refine le_trans hz ?_
      exact_mod_cast le_trans (le_max_right N₀ M) hN
    have h1 := htail N z hzN
    have h2 := hN₀ N (le_trans (le_max_left N₀ M) hN)
    rw [Real.dist_eq, sub_zero] at h2
    rw [dist_eq_norm]
    calc ‖w z - v N z‖ ≤ 2 * (1 / 2 : ℝ) ^ N := h1
      _ ≤ |2 * (1 / 2 : ℝ) ^ N| := le_abs_self _
      _ < ε := h2
  have hwcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro z
    obtain ⟨M, hM⟩ := exists_nat_gt ‖z‖
    have hzball : z ∈ Metric.ball (0 : Fin n → ℂ) (M : ℝ) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hM
    have hcon : ContinuousOn w (Metric.closedBall (0 : Fin n → ℂ) (M : ℝ)) :=
      (hunif M).continuousOn
        (Filter.Eventually.frequently
          (Filter.Eventually.of_forall fun N => (hCv N).continuous.continuousOn))
    exact hcon.continuousAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzball)
      Metric.ball_subset_closedBall)
  have hGholo : ∀ N k : ℕ, DifferentiableOn ℂ (fun z => v (k + N) z - v N z)
      (Metric.ball (0 : Fin n → ℂ) (N : ℝ)) := by
    intro N k
    induction k with
    | zero =>
        simpa using differentiableOn_const (0 : ℂ)
    | succ k ih =>
        have heq : (fun z => v (k + 1 + N) z - v N z)
            = fun z => (v (k + N + 1) z - v (k + N) z) + (v (k + N) z - v N z) := by
          funext z
          rw [show k + 1 + N = k + N + 1 by ring]
          ring
        rw [heq]
        refine DifferentiableOn.add ?_ ih
        refine (hholo (k + N)).mono (Metric.ball_subset_ball ?_)
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
  have hwvN : ∀ N : ℕ, DifferentiableOn ℂ (fun z => w z - v N z)
      (Metric.ball (0 : Fin n → ℂ) (N : ℝ)) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      rw [Nat.cast_zero, Metric.ball_zero]
      exact differentiableOn_empty
    refine differentiableOn_of_tendstoUniformlyOn (by exact_mod_cast hNpos)
      (fun k => ((hCv (k + N)).continuous.sub (hCv N).continuous).continuousOn)
      (fun k => hGholo N k) ((hwcont.sub (hCv N).continuous).continuousOn) ?_
    intro ρ hρ0 hρN
    obtain ⟨M, hM⟩ := exists_nat_gt ρ
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hbase := Metric.tendstoUniformlyOn_iff.1 (hunif M) ε hε
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hbase
    filter_upwards [Filter.eventually_ge_atTop N₁] with k hk z hz
    have hzM : z ∈ Metric.closedBall (0 : Fin n → ℂ) (M : ℝ) := by
      rw [Metric.mem_closedBall] at hz ⊢
      exact le_trans hz hM.le
    have := hN₁ (k + N) (le_trans hk (Nat.le_add_right k N)) z hzM
    rw [dist_eq_norm] at this ⊢
    have heq : w z - v N z - (v (k + N) - v N) z = w z - v (k + N) z := by
      show w z - v N z - (v (k + N) z - v N z) = w z - v (k + N) z
      ring
    rw [heq]
    exact this
  have hrecomb : ∀ N : ℕ, (fun y => (w y - v N y) + v N y) = w := by
    intro N
    funext y
    ring
  have hwsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    rw [contDiff_iff_contDiffAt]
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    have hzball : z ∈ Metric.ball (0 : Fin n → ℂ) (N : ℝ) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hN
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => w y - v N y) z :=
      contDiffAt_of_differentiableOn Metric.isOpen_ball (hwvN N) hzball
    have h2 := h1.add (hCv N).contDiffAt
    rwa [hrecomb N] at h2
  refine ⟨w, hwsmooth, ?_⟩
  intro j z
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  have hzball : z ∈ Metric.ball (0 : Fin n → ℂ) (N : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hN
  have hdvN : Differentiable ℝ (v N) := (hCv N).differentiable (by simp)
  have hdw : Differentiable ℝ (fun y => w y - v N y) :=
    (hwsmooth.differentiable (by simp)).sub hdvN
  have hsplit : dzbarAt w j z = dzbarAt (fun y => w y - v N y) j z + dzbarAt (v N) j z := by
    have h := dzbarAt_add hdw hdvN j z
    rwa [hrecomb N] at h
  rw [hsplit, dzbarAt_eq_zero_of_differentiableOn Metric.isOpen_ball (hwvN N) hzball j, zero_add]
  refine hsolve N j z (Metric.ball_subset_ball ?_ hzball)
  linarith

end MittagLeffler

end HTGeometry
