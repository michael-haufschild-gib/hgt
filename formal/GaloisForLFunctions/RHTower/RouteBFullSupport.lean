/-
Reducing the full-support carrier over `[1,N]` to a four-phase dominant block plus an independent
remainder, in the completely multiplicative Steinhaus model.

The block small-ball law bounds `‖w + Σ_{n∈s} aₙ Xₙ‖ ≤ t` for a prime-supported block `s`, uniformly
in the shift `w`. The certificate carrier `dirichletPoly N` has full support `[1,N]`, whose composite
terms are products of prime phases and hence correlated with any prime block — so the naive
"absorb composites into an independent shift" fails. The remedy is to pick the four dominant primes in
`(N/2, N]`: then no `n ≤ N` is divisible by any `pᵢ` except `pᵢ` itself, so the carrier splits as the
four pure terms `Σᵢ a_{pᵢ} X_{pᵢ}` plus a remainder over integers divisible by none of the `pᵢ`. Since
`X n ω = exp(2πi Σ_{q | n} v_q(n) ω_q)` reads only prime-factor coordinates, the remainder involves no
`pᵢ`-coordinate and is therefore independent of the four dominant phases — exactly the rest-measurable
shift the block law integrates against.
-/
import GaloisForLFunctions.RHTower.RouteBBlockStep

open Complex Finset
open MeasureTheory
open RHTower.SteinhausModel

namespace RHTower

/-- **Isolation of a large divisor.** If `1 ≤ n ≤ N`, `N < 2p`, and `p ∣ n`, then `n = p`: the only
multiple of `p` in `[1, N]` when `p > N/2` is `p` itself. Writing `n = p·k`, the bounds `1 ≤ p·k` and
`p·k ≤ N < 2p` force `k = 1`. -/
theorem eq_of_dvd_of_mem_Icc_of_lt_two_mul {N p n : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hN : N < 2 * p) (hdvd : p ∣ n) : n = p := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk] at h1
    · exact hk
  have hk2 : k < 2 := by
    by_contra hc
    rw [not_lt] at hc
    have : 2 * p ≤ p * k := by
      calc 2 * p = p * 2 := by ring
        _ ≤ p * k := Nat.mul_le_mul_left p hc
    omega
  have : k = 1 := by omega
  rw [this, mul_one]

/-- **The dominant multiples are exactly the four primes.** With four large primes `p₁,…,p₄ ∈ [1,N]`
each exceeding `N/2` (so `N < 2pᵢ`), the integers in `[1,N]` divisible by some `pᵢ` are precisely
`{p₁,p₂,p₃,p₄}`. Each `pᵢ` is divisible by itself and in range; conversely a divisible `n` is isolated
onto its dominant prime. -/
theorem dominant_multiples_eq {N p1 p2 p3 p4 : ℕ}
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4) :
    (Finset.Icc 1 N).filter (fun n => p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)
      = {p1, p2, p3, p4} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hnI, hdvd⟩
    rcases hdvd with h | h | h | h
    · exact Or.inl (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN1 h)
    · exact Or.inr (Or.inl (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN2 h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN3 h)))
    · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN4 h)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨hp1I, Or.inl dvd_rfl⟩
    · exact ⟨hp2I, Or.inr (Or.inl dvd_rfl)⟩
    · exact ⟨hp3I, Or.inr (Or.inr (Or.inl dvd_rfl))⟩
    · exact ⟨hp4I, Or.inr (Or.inr (Or.inr dvd_rfl))⟩

/-- **Carrier dominant-block decomposition.** With four distinct large primes `p₁,…,p₄` in `[1,N]`
(each `> N/2`), any finite carrier over `[1,N]` splits as the four dominant terms plus a sum over the
integers divisible by none of the `pᵢ`. -/
theorem carrier_dominant_decomp {N p1 p2 p3 p4 : ℕ} (f : ℕ → ℂ)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4) :
    ∑ n ∈ Finset.Icc 1 N, f n
      = (f p1 + f p2 + f p3 + f p4)
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ (p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)), f n := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
        (fun n => p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n) f]
  congr 1
  rw [dominant_multiples_eq hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4]
  rw [show ({p1, p2, p3, p4} : Finset ℕ) = insert p1 (insert p2 (insert p3 {p4})) from rfl]
  rw [Finset.sum_insert (by simp [h12, h13, h14]),
      Finset.sum_insert (by simp [h23, h24]),
      Finset.sum_insert (by simp [h34]),
      Finset.sum_singleton]
  ring

/-- **The character reads only prime-factor coordinates.** If `ω` and `ω'` agree on every prime factor
of `n`, then `X n ω = X n ω'`. -/
theorem X_congr_of_eqOn_primeFactors (n : ℕ) {ω ω' : Omega}
    (h : ∀ q ∈ n.primeFactors, ω q = ω' q) : X n ω = X n ω' := by
  unfold X
  congr 3
  apply Finset.sum_congr rfl
  intro q hq
  rw [h q hq]

/-- A prime not dividing `n` is not among its prime factors. -/
theorem not_mem_primeFactors_of_not_dvd {p n : ℕ} (hdvd : ¬ p ∣ n) :
    p ∉ n.primeFactors := by
  rw [Nat.mem_primeFactors]
  rintro ⟨_, hpn, _⟩
  exact hdvd hpn

/-- **Rest terms avoid the block coordinates.** For `n` divisible by none of the four primes, none of
`p₁,…,p₄` is a prime factor of `n`; hence `X n` reads only coordinates outside `{p₁,p₂,p₃,p₄}`, so the
remainder sum is independent of the four dominant phases. -/
theorem primeFactors_disjoint_block {p1 p2 p3 p4 n : ℕ}
    (hn : ¬ (p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)) :
    Disjoint n.primeFactors ({p1, p2, p3, p4} : Finset ℕ) := by
  rw [not_or, not_or, not_or] at hn
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hn
  rw [Finset.disjoint_right]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact not_mem_primeFactors_of_not_dvd hd1
  · exact not_mem_primeFactors_of_not_dvd hd2
  · exact not_mem_primeFactors_of_not_dvd hd3
  · exact not_mem_primeFactors_of_not_dvd hd4

/-- Interface: the four-phase block small-ball bound holds with a **complement-measurable random
shift** `W`. `W` may depend on `ω` only through coordinates outside `{p₁,p₂,p₃,p₄}`; then the
small-ball probability of `W + Σᵢ a_{pᵢ} X_{pᵢ}` is at most `(2π)⁻⁴ M`. This generalizes the
constant-shift block law by integrating the uniform four-phase bound over the independent complement:
marginalizing the model measure over the four dominant coordinates leaves the inner four-phase
integral bounded by `M` uniformly in the frozen value of `W`, and the complement integrates that
constant against a probability measure. -/
def BlockSmallBallRandomShift (p1 p2 p3 p4 : ℕ) (a : ℕ → ℝ) (t : ℝ) (M : ENNReal) : Prop :=
  ∀ W : Omega → ℂ,
    (∀ ω ω' : Omega, (∀ q, q ∉ ({p1, p2, p3, p4} : Finset ℕ) → ω q = ω' q) → W ω = W ω') →
    steinhausMeasure {ω : Omega | ‖W ω + (a p1 : ℂ) * X p1 ω + (a p2 : ℂ) * X p2 ω
        + (a p3 : ℂ) * X p3 ω + (a p4 : ℂ) * X p4 ω‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M

/-- **Finite random-center four-phase bound.**  In a finite product of
uniform phases, a measurable center `W` that is unchanged by updating the four
peeled coordinates may be frozen while those four coordinates are integrated.
Thus the center-uniform four-phase estimate applies pointwise to the frozen
complement and then integrates back to the same bound. -/
theorem four_phase_pi_le_randomShift {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : (ι → ℝ) → ℂ) (hWm : Measurable W)
    (q1 q2 q3 q4 : ι) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4)
    (D C B A : ℂ) (t : ℝ) (M : ENNReal)
    (hWinv : ∀ (y : ι → ℝ) (x1 x2 x3 x4 : ℝ),
      W (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) = W y)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0 : ℝ) (2 * Real.pi),
        ∫⁻ θC in Set.Icc (0 : ℝ) (2 * Real.pi),
        ∫⁻ θB in Set.Icc (0 : ℝ) (2 * Real.pi),
        ∫⁻ θA in Set.Icc (0 : ℝ) (2 * Real.pi),
          {θ' : ℝ | ‖V + D * Complex.exp ((θD : ℂ) * Complex.I)
              + C * Complex.exp ((θC : ℂ) * Complex.I)
              + B * Complex.exp ((θB : ℂ) * Complex.I)
              + A * Complex.exp ((θ' : ℂ) * Complex.I)‖ ≤ t}.indicator
            (fun _ => (1 : ENNReal)) θA) ≤ M) :
    (Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1))
        {x : ι → ℝ | ‖W x + D * unitPhase (x q1) + C * unitPhase (x q2)
            + B * unitPhase (x q3) + A * unitPhase (x q4)‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  haveI : ∀ i : ι, IsProbabilityMeasure
      ((fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)) i) :=
    fun _ => ⟨by simp⟩
  set μ : ι → Measure ℝ := fun _ => volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  set E' : Set (ι → ℝ) :=
    {x | ‖W x + D * unitPhase (x q1) + C * unitPhase (x q2)
      + B * unitPhase (x q3) + A * unitPhase (x q4)‖ ≤ t} with hE'
  have hq1m : Measurable fun x : ι → ℝ => unitPhase (x q1) := by
    unfold unitPhase
    fun_prop
  have hq2m : Measurable fun x : ι → ℝ => unitPhase (x q2) := by
    unfold unitPhase
    fun_prop
  have hq3m : Measurable fun x : ι → ℝ => unitPhase (x q3) := by
    unfold unitPhase
    fun_prop
  have hq4m : Measurable fun x : ι → ℝ => unitPhase (x q4) := by
    unfold unitPhase
    fun_prop
  have hsum_m : Measurable fun x : ι → ℝ =>
      W x + D * unitPhase (x q1) + C * unitPhase (x q2)
        + B * unitPhase (x q3) + A * unitPhase (x q4) := by
    exact ((((hWm.add (measurable_const.mul hq1m)).add
      (measurable_const.mul hq2m)).add
      (measurable_const.mul hq3m)).add
      (measurable_const.mul hq4m))
  have hE'm : MeasurableSet E' := by
    rw [hE']
    exact measurableSet_le hsum_m.norm measurable_const
  have hfm : Measurable (E'.indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hE'm
  have hpiE : (Measure.pi μ) E' =
      ∫⁻ x, E'.indicator (fun _ => (1 : ENNReal)) x ∂(Measure.pi μ) := by
    rw [lintegral_indicator hE'm, setLIntegral_one]
  change (Measure.pi μ) E' ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M
  rw [hpiE, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0 : ℝ))]
  rw [show (Finset.univ : Finset ι)
        = (Finset.univ \ {q1, q2, q3, q4}) ∪ {q1, q2, q3, q4} from
      (Finset.sdiff_union_of_subset (Finset.subset_univ _)).symm]
  rw [lmarginal_union μ _ hfm Finset.sdiff_disjoint]
  have hbound : (fun z =>
        (∫⋯∫⁻_{q1, q2, q3, q4}, E'.indicator (fun _ => (1 : ENNReal)) ∂μ) z)
      ≤ fun _ => ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
    intro y
    set V : ℂ := W y with hV
    set Gfun : ℝ → ℝ → ℝ → ℝ → ENNReal := fun θ1 θ2 θ3 θ4 =>
      {z : ℂ | ‖z‖ ≤ t}.indicator (fun _ => (1 : ENNReal))
        (V + D * Complex.exp ((θ1 : ℂ) * Complex.I)
          + C * Complex.exp ((θ2 : ℂ) * Complex.I)
          + B * Complex.exp ((θ3 : ℂ) * Complex.I)
          + A * Complex.exp ((θ4 : ℂ) * Complex.I)) with hGfun
    have hSm : MeasurableSet {z : ℂ | ‖z‖ ≤ t} :=
      (isClosed_le continuous_norm continuous_const).measurableSet
    dsimp
    rw [peel4 μ _ hfm q1 q2 q3 q4 h12 h13 h14 h23 h24 h34 y]
    have he : ∀ x : ℝ, unitPhase x =
        Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      intro x
      unfold unitPhase
      congr 1
      push_cast
      ring
    have hpt : ∀ x1 x2 x3 x4 : ℝ,
        E'.indicator (fun _ => (1 : ENNReal))
          (Function.update (Function.update (Function.update
            (Function.update y q1 x1) q2 x2) q3 x3) q4 x4)
        = Gfun (2 * Real.pi * x1) (2 * Real.pi * x2)
            (2 * Real.pi * x3) (2 * Real.pi * x4) := by
      intro x1 x2 x3 x4
      have hval :
          W (Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4)
            + D * unitPhase ((Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q1)
            + C * unitPhase ((Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q2)
            + B * unitPhase ((Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q3)
            + A * unitPhase ((Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q4)
          = V + D * Complex.exp (((2 * Real.pi * x1 : ℝ) : ℂ) * Complex.I)
            + C * Complex.exp (((2 * Real.pi * x2 : ℝ) : ℂ) * Complex.I)
            + B * Complex.exp (((2 * Real.pi * x3 : ℝ) : ℂ) * Complex.I)
            + A * Complex.exp (((2 * Real.pi * x4 : ℝ) : ℂ) * Complex.I) := by
        rw [hWinv y x1 x2 x3 x4, hV]
        simp [Function.update_self, Function.update_of_ne, h12, h13, h14, h23, h24, h34, he]
      simp only [hE', hGfun, Set.indicator_apply, Set.mem_setOf_eq, hval]
    simp_rw [hμ, hpt]
    rw [rescale4 Gfun (by
      simp only [hGfun]
      exact (measurable_const.indicator hSm).comp (by fun_prop))]
    refine mul_le_mul_right ?_ _
    refine le_trans (le_of_eq ?_) (hM V)
    simp only [hGfun, Set.indicator_apply, Set.mem_setOf_eq]
  refine le_trans (lmarginal_mono hbound _) (le_of_eq ?_)
  rw [lmarginal]
  simp only [lintegral_const]
  rw [measure_univ, mul_one]

/-- **Finite random-center caustic bound.**  The center-uniform caustic
four-phase theorem feeds the finite random-center bridge directly: any
measurable center frozen off the four coordinates has the same explicit
four-phase small-ball bound as a constant center. -/
theorem four_phase_pi_le_randomShift_of_caustic {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : (ι → ℝ) → ℂ) (hWm : Measurable W)
    (q1 q2 q3 q4 : ι) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4)
    {D C B A : ℂ} {t σ0 sstar : ℝ} {J : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hρB : ‖B‖ < ‖A‖) (hr0 : 0 < t) (hr2 : 2 * t ≤ ‖A‖ - ‖B‖)
    (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3)
    (hJ : ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (t * (2 * ‖A‖ + t) / ((‖A‖ - ‖B‖) * ‖B‖))
        ≤ σ0 * Sublevel.causticKappa ‖A‖ ‖B‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖D‖)
    (hWinv : ∀ (y : ι → ℝ) (x1 x2 x3 x4 : ℝ),
      W (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) = W y) :
    (Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1))
        {x : ι → ℝ | ‖W x + D * unitPhase (x q1) + C * unitPhase (x q2)
            + B * unitPhase (x q3) + A * unitPhase (x q4)‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
          * Sublevel.fourPhaseConst A B C D t σ0 sstar J := by
  exact four_phase_pi_le_randomShift W hWm q1 q2 q3 q4 h12 h13 h14 h23 h24 h34
    D C B A t (Sublevel.fourPhaseConst A B C D t σ0 sstar J) hWinv
    (fun V => Sublevel.four_phase_nested_uniform hA hB hC hD hρB hr0 hr2
      hσ0 hσ0G hJ hHσ0 hss hss2)

/-- **Full-support carrier small-ball from the random-shift block law.** With four distinct large
primes `p₁,…,p₄ ∈ (N/2, N]`, the full-support carrier over `[1,N]` splits (via `carrier_dominant_decomp`)
into the four dominant terms plus a remainder over integers divisible by none of the `pᵢ`; that
remainder reads only complement coordinates (`primeFactors_disjoint_block` + `X_congr_of_eqOn_primeFactors`),
so it is an admissible random shift. Hence the small-ball probability of the whole carrier is at most
`(2π)⁻⁴ M`. This reduces the full-support anti-concentration to the single random-shift block law. -/
theorem fullCarrier_smallball_of_randomShift {N : ℕ} (a : ℕ → ℝ) {t : ℝ} {M : ENNReal}
    {p1 p2 p3 p4 : ℕ}
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hRS : BlockSmallBallRandomShift p1 p2 p3 p4 a t M) :
    steinhausMeasure {ω : Omega | ‖∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  set W : Omega → ℂ :=
    fun ω => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ (p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)),
      (a n : ℂ) * X n ω with hW
  have hWmeas : ∀ ω ω' : Omega,
      (∀ q, q ∉ ({p1, p2, p3, p4} : Finset ℕ) → ω q = ω' q) → W ω = W ω' := by
    intro ω ω' hqq
    rw [hW]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_filter] at hn
    have hdisj := primeFactors_disjoint_block hn.2
    have hpf : ∀ q ∈ n.primeFactors, ω q = ω' q := by
      intro q hq
      exact hqq q (Finset.disjoint_left.mp hdisj hq)
    rw [X_congr_of_eqOn_primeFactors n hpf]
  have hsplit : ∀ ω : Omega, ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω
      = W ω + (a p1 : ℂ) * X p1 ω + (a p2 : ℂ) * X p2 ω
          + (a p3 : ℂ) * X p3 ω + (a p4 : ℂ) * X p4 ω := by
    intro ω
    rw [carrier_dominant_decomp (fun n => (a n : ℂ) * X n ω)
      hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34]
    rw [hW]; ring
  have hset : {ω : Omega | ‖∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω‖ ≤ t}
      = {ω : Omega | ‖W ω + (a p1 : ℂ) * X p1 ω + (a p2 : ℂ) * X p2 ω
          + (a p3 : ℂ) * X p3 ω + (a p4 : ℂ) * X p4 ω‖ ≤ t} := by
    ext ω
    simp only [Set.mem_setOf_eq, hsplit ω]
  rw [hset]
  exact hRS W hWmeas

end RHTower
