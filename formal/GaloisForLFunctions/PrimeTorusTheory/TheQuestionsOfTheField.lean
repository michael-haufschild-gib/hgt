import GaloisForLFunctions.PrimeTorusTheory.TheSavingAgainstSize
import GaloisForLFunctions.PrimeTorusTheory.TheRoundedOrbit
import GaloisForLFunctions.PrimeTorusTheory.TheRankLaw
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus
import GaloisForLFunctions.PrimeTorusTheory.TheReturnsThePoleMustPay
import GaloisForLFunctions.PrimeTorusTheory.CertificatesOnTheOrbit
import GaloisForLFunctions.PrimeTorusTheory.TheCriticalCouplingOfTheBase
import GaloisForLFunctions.PrimeTorusTheory.TheDiscrepancyOfTheOrbit
import GaloisForLFunctions.PrimeTorusTheory.PrimeByPrimePaymentCannotUseTheGammaFactor
import GaloisForLFunctions.PrimeTorusTheory.TheWallForAllPrimes
import GaloisForLFunctions.PrimeTorusTheory.TheCertificateAtRankOne
import GaloisForLFunctions.PrimeTorusTheory.TheSavingOnAnySetOfPrimes
import GaloisForLFunctions.PrimeTorusTheory.TheSavingAtEveryLength
import GaloisForLFunctions.PrimeTorusTheory.TheBoxesOfTheTorus
import GaloisForLFunctions.PrimeTorusTheory.TheEnergyPastTheDiagonal
import GaloisForLFunctions.PrimeTorusTheory.TheSavingAwayFromSmallPrimes
import GaloisForLFunctions.PrimeTorusTheory.CoordinatesThatSeeTheHeight
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTorsionPoints
import GaloisForLFunctions.PrimeTorusTheory.TheNaturalBoundaryOfTheHull
import GaloisForLFunctions.PrimeTorusTheory.TheBoxesAtSquareRootCost
import GaloisForLFunctions.PrimeTorusTheory.TheLiftOfTheXiCurrent
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverOrderTwoPoints

/-!
# The questions of the field

Each of the six questions of prime torus theory, with its answer as one statement.

1. How long does the orbit need to enter a half-space at length `y = (log T)^{2K}`, and is there any saving against size? (`question_one`)
2. What is the near-diagonal energy past `k = log T / log y`? (`question_two`)
3. Why does the Gamma coupling sit at the critical growth `½`? (`question_three`)
4. Which functions on `X` restrict to the Ξ-current and have a sum-of-squares form with `t`-dependent coefficients? (`question_four`, `question_four_xi_current`)
5. Over which torus points does the hull extend into the strip, and which of those carry zeros? (`question_five`)
6. Does a large-value set of heights have additive structure, and does it force returns that the pole must pay for? (`question_six`)
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- **Question 1.** Every window of length `exp(c_m y)` enters every half-space on the primes up to `y` at level `m/(m+1)`, whatever the length `N` of the polynomial. Past the Kronecker scale the critical column never reaches its size: the saving exceeds every negative power of `|t|` at every length `(log |t|)^A`, `A > 1`, and is a negative power of `log |t|` at length `(log |t|)² log log |t|`. Deleting every prime up to `(log T)^{A'}` keeps a saving that is a negative power of `T`. -/
theorem question_one {A A' δ : ℝ} (hA' : 1 < A') (hAA' : A' < A) (hδ : 0 < δ) :
    (∀ {y N m : ℕ} (θ : ℕ → ℝ) {η : ℝ} (T : ℝ) {L : ℝ}, y ≤ N → 1 ≤ m → 0 < η → η ≤ 1 →
      2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ y * (4 : ℝ) ^ (m * y) < η * L →
      ∃ t ∈ Set.Icc T (T + L),
        (m : ℝ) / (m + 1) * ∑ p ∈ primesUpTo y, (p : ℝ) ^ (-(1 / 2 : ℝ)) -
            η * ∑ r ∈ primesUpTo N, (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          ∑ r ∈ primesUpTo N, (r : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log r - θ r)) ∧
      (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ, Real.log |t| ^ A ≤ N →
        |t| ^ (-δ) ≤ ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ)) ∧
      (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
        48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
        4 / 10 ^ 10 / (Real.log |t| ^ 8 * Real.log (Real.log |t|) ^ 4) ≤
          ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ)) ∧
      ∃ T₀ : ℝ, ∀ T, T₀ ≤ T → ∀ t ∈ Set.Icc T (2 * T),
        T ^ (-(2 * (A - A' + 1) / (A' - 1) + δ)) ≤
          ∑ p ∈ topPrimes (Real.log T ^ A') ⌊Real.log T ^ A⌋₊,
            (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.cos (t * Real.log p)) :=
  ⟨fun θ _ T _ hyN hm hη hη1 hL =>
    exists_column_ge_of_primesUpTo hyN hm (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) θ hη hη1 T hL,
    rpow_neg_le_sum_primes_critical (hA'.trans hAA') hδ, le_sum_primes_critical,
    saving_at_the_top_of_the_column hA' hAA' hδ⟩

variable {Q : Finset ℕ}

open Classical in
/-- The energy contains the diagonal. -/
theorem diagonalMass_le_energy [DecidableEq Q] (hQ : ∀ r ∈ Q, r.Prime) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r)
    (k : ℕ) (H : ℝ) :
    diagonalMass Q a ha k ≤ (primeSystem Q a ha).energy k H := by
  unfold diagonalMass PhaseSystem.energy
  refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
  have hw : 0 ≤ (primeSystem Q a ha).tupleWeight u * (primeSystem Q a ha).tupleWeight v :=
    mul_nonneg (PhaseSystem.tupleWeight_nonneg _ u) (PhaseSystem.tupleWeight_nonneg _ v)
  by_cases h : tupleProd u = tupleProd v
  · rw [if_pos h, primeSystem_tupleStep hQ a ha u, primeSystem_tupleStep hQ a ha v, h]
    simp
  · rw [if_neg h]
    exact mul_nonneg hw (sq_nonneg _)

/-- **Question 2.** The energy is the clocked moment of the orbit. Through the diagonal range it is the diagonal; past it, it contains the start of the orbit, which is the mixing term, and it is bounded above by size. Absolute values on the pairs never see a
saving: non-alignment lives in the cancellation of the oscillating sum, and diagonal data cannot exclude a return. -/
theorem question_two [DecidableEq Q] (hQ : ∀ r ∈ Q, r.Prime)
    {y : ℕ} (hy : ∀ r ∈ Q, r ≤ y) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) {Λ : ℝ} (hΛ0 : 0 < Λ)
    (hΛ : ∀ r ∈ Q, Real.log r ≤ Λ) {k : ℕ} (hk : 1 ≤ k) {H : ℝ} (hH : 0 < H)
    (hHΛ : 1 / (2 * k * Λ) ≤ H) :
    (∀ T₀, (primeSystem Q a ha).clockedMoment k T₀ H = (primeSystem Q a ha).shiftedEnergy k T₀ H) ∧
      (∀ T₀, |(primeSystem Q a ha).shiftedEnergy k T₀ H| ≤ (primeSystem Q a ha).energy k H) ∧
      diagonalMass Q a ha k ≤ (primeSystem Q a ha).energy k H ∧
      (∑ r ∈ Q, a r) ^ (2 * k) / (8 * k * Λ * H) ≤ (primeSystem Q a ha).energy k H ∧
      (primeSystem Q a ha).energy k H ≤
        k.factorial * (∑ r ∈ Q, a r ^ 2) ^ k * (1 + 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2) := by
  have hstep : ∀ i, |(primeSystem Q a ha).step i| ≤ Λ := by
    intro r
    have h0 : 0 ≤ Real.log ((r : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [show (primeSystem Q a ha).step r = Real.log ((r : ℕ) : ℝ) from rfl, abs_of_nonneg h0]
    exact hΛ _ r.2
  refine ⟨fun T₀ => PhaseSystem.clockedMoment_eq _ k T₀ hH, fun T₀ => PhaseSystem.abs_shiftedEnergy_le_energy _ k T₀ H,
    diagonalMass_le_energy hQ a ha k H, ?_, energy_le hQ hy a ha k hH⟩
  have h := PhaseSystem.energy_ge_start (S := primeSystem Q a ha) hk hΛ0 hstep hH hHΛ
  rwa [primeSystem_size] at h

/-- **Question 3.** The theta amplitude counts integers: its left growth is exactly `½` by Poisson summation, its diagonal cost balances exactly against integer tests, loses one logarithm against primes, and vanishes below `½`. Both `½`s are the pole of `ζ`. -/
theorem question_three :
    Tendsto (fun x => thetaAmp x * Real.exp (x / 2)) atBot (𝓝 (1 / 2)) ∧
      (∀ y, Tendsto (fun u => thetaAmp (y - 2 * u) * Real.exp (-u)) atTop (𝓝 (Real.exp (-(y / 2)) / 2))) ∧
      (∀ y, Tendsto (fun u => thetaAmp (y - 2 * u) / Nat.primeCounting ⌊Real.exp (u + 1)⌋₊) atTop atTop) ∧
      ∀ κ : ℝ, κ < 1 / 2 →
        Tendsto (fun u : ℝ => Real.exp (2 * κ * u) * (u + 1) * Real.exp (-u)) atTop (𝓝 0) :=
  ⟨tendsto_thetaAmp_left, tendsto_thetaAmp_integers, tendsto_thetaAmp_div_primeCounting,
    fun _ h => tendsto_cost_of_lt_half h⟩

/-- **Question 4.** Coefficients that vary with `t` freely give a tautology. Coefficients frozen on a window longer than the Kronecker time cost size. Above the size curve the certificate is explicit, column by column. A kernel-valued certificate with returning prime coordinates and a Gamma coordinate cannot pay more than the Gamma coordinate dominates, for finitely many primes on `Re s > 0` and for all primes on `Re s > σ₀ ≥ ½`; a Schur function carrying the Euler factor of the scattering function has none. At one coordinate every Schur function has a certificate with no Gamma factor. -/
theorem question_four :
    (∀ f : ℝ → ℝ, (∀ t, 0 ≤ f t) → ∃ h : ℝ → ℝ, ∀ t, h t ^ 2 = f t) ∧
      (∀ {y N m : ℕ} {a : ℕ → ℝ} {η B T L : ℝ}, y ≤ N → 1 ≤ m → (∀ r ∈ primesUpTo N, 0 ≤ a r) → 0 < η → η ≤ 1 →
        2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ y * (4 : ℝ) ^ (m * y) < η * L →
        (∀ t ∈ Set.Icc T (T + L), ∑ r ∈ primesUpTo N, a r * Real.cos (t * Real.log r) ≤ B) →
        (m : ℝ) / (m + 1) * ∑ p ∈ primesUpTo y, a p - η * ∑ r ∈ primesUpTo N, a r ≤ B) ∧
      (∀ {r ℓ b : ℝ}, 0 ≤ r → r < 1 → 0 ≤ ℓ → ℓ * (r / (1 - r)) ≤ b →
        ∃ u v : ℝ, 0 ≤ v ∧ v ≤ u ∧ ∀ w : ℂ, ‖w‖ = 1 →
          b - ℓ * ArithmeticInnerFunctionTheory.colShape r w.re = ‖((u : ℂ) - v * w) / (1 - r * w)‖ ^ 2) ∧
      (∀ {P : Finset ℕ}, (∀ p ∈ P, p.Prime) → ∀ {S G : HalfPlane → ℂ}, AglerDecomposition S G (primeCoord P) →
        (∀ x, ‖G x‖ < 1) → (∀ s, Tendsto (fun τ => G (vshift s τ)) atTop (𝓝 0)) →
        (∀ s, Tendsto (fun τ => S (vshift s τ)) atTop (𝓝 0)) → ∀ s, ‖S s‖ ≤ ‖G s‖) ∧
      (∀ {σ₀ : ℝ} [Fact ((1 : ℝ) / 2 ≤ σ₀)] {S G : Plane σ₀ → ℂ}, AglerDecompositionAll S G →
        (∀ x, ‖G x‖ < 1) → (∀ s, Tendsto (fun τ => G (vshift' s τ)) atTop (𝓝 0)) →
        (∀ s, Tendsto (fun τ => S (vshift' s τ)) atTop (𝓝 0)) → ∀ s, ‖S s‖ ≤ ‖G s‖) ∧
      ((∀ s, ‖eulerTestS s‖ < 1) ∧ IsEmpty (AglerDecompositionAll eulerTestS eulerTestG)) ∧
      ∀ {q : ℕ} {f : ℂ → ℂ}, 2 ≤ q → DifferentiableOn ℂ f (Metric.ball 0 1) →
        Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) →
        Nonempty (AglerDecomposition (fun s => f (rankOneCoord q s)) (fun _ => 0)
          (fun _ : Unit => rankOneCoord q)) :=
  ⟨fun _ hf => graph_lift hf, fun hyN hm ha hη hη1 hL hB =>
    frozen_certificate_costs_size hyN hm ha hη hη1 hL hB,
    fun hr0 hr1 hℓ hb => column_outer_factor hr0 hr1 hℓ hb,
    fun hP _ _ D hG hGv hSv s => agler_wall hP D hG hGv hSv s,
    fun D hG hGv hSv s => agler_wall_all_primes D hG hGv hSv s,
    ⟨euler_test.1, euler_test.2.2⟩,
    fun hq hd hm => (rank_one_law hq hd hm).1⟩

open ArithmeticCorrelationGeometry in
/-- **Question 5.** The Liouville fibre extends to `Re s > ½` if and only if RH holds; a Haar-typical fibre extends, is zero-free, and has the critical line as natural boundary; almost every order-two point extends and is zero-free; a finite modification of an orbit point carries exactly the translated zeros of `ζ`; and RH is the zero-freeness of every
nonzero limit of vertical translates. -/
theorem question_five :
    (RiemannHypothesis ↔ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalf ∧ ∀ s, 1 < s.re → F s = liouvilleFibre s) ∧
      (∀ᵐ x ∂gaugeHaar, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
        (∀ s, 1 < s.re → F s = gaugeFibre x s) ∧ (∀ s ∈ rightHalf, F s ≠ 0) ∧
        ∀ (τ₀ r : ℝ) (H : ℂ → ℂ), 0 < r → AnalyticOnNhd ℂ H (Metric.ball (⟨1 / 2, τ₀⟩ : ℂ) r) →
          ¬ ∀ s ∈ Metric.ball (⟨1 / 2, τ₀⟩ : ℂ) r, s ∈ rightHalf → H s = F s) ∧
      (∀ᵐ ω ∂signMeasure, (∀ p, p.Prime → _root_.RHTower.SteinhausModel.X p ω = 1 ∨
          _root_.RHTower.SteinhausModel.X p ω = -1) ∧
        ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
          (∀ s, 1 < s.re → F s = ∑' n, signHom ω n * (n : ℂ) ^ (-s)) ∧ ∀ s ∈ rightHalf, F s ≠ 0) ∧
      (∀ {g : ℕ →*₀ ℂ}, (∀ n, ‖g n‖ ≤ 1) → ∀ (u : ℝ) (F : Finset Nat.Primes) {s : ℂ}, 0 < s.re →
        (riemannZeta (s + (u : ℂ) * Complex.I) *
          ∏ p ∈ F, ((1 - orbitPoint u p * ((p : ℕ) : ℂ) ^ (-s)) * (1 - g p * ((p : ℕ) : ℂ) ^ (-s))⁻¹) = 0 ↔
          riemannZeta (s + (u : ℂ) * Complex.I) = 0)) ∧
      (RiemannHypothesis ↔ ∀ (U : Set ℂ) (τ : ℕ → ℝ) (F : ℂ → ℂ), IsOpen U → IsPreconnected U →
        U ⊆ rightHalf → (∀ j, ∀ s ∈ U, s + (τ j : ℂ) * Complex.I ≠ 1) →
        TendstoLocallyUniformlyOn (fun j s => riemannZeta (s + (τ j : ℂ) * Complex.I)) F atTop U →
        (∃ a ∈ U, F a ≠ 0) → ∀ s ∈ U, F s ≠ 0) :=
  ⟨riemannHypothesis_iff_liouvilleFibre_extends, ae_natural_boundary, ae_signFibre_extends_zeroFree,
    fun hg u F _ hs => fibre_zero_iff hg u F hs, riemannHypothesis_iff_limits_zeroFree⟩

/-- **Question 6.** Heights at level `θ` have differences at level `θ²` on average, and at weights `1/p` the pole prices every level: a height at level `θ` lies above `exp(c (log z)^θ)`. Rare heights are counted by the first return. -/
theorem question_six {ι : Type*} [Fintype ι] (S : PhaseSystem ι) :
    (∀ {A : Finset ℝ} {θ : ℝ}, 0 ≤ θ → 0 < S.size → (∀ t ∈ A, t ∈ S.largeValue θ) →
      θ ^ 2 * (A.card : ℝ) ^ 2 * S.size ≤ ∑ t ∈ A, ∑ u ∈ A, S.column (t - u)) ∧
      (∀ {r t u : ℝ}, 0 ≤ r → t ∈ S.bohr r → u ∈ S.bohr r → t - u ∈ S.bohr (2 * r)) ∧
      (∀ {z : ℕ} {u θ : ℝ}, 3 ≤ z → 8 ≤ |u| → u ∈ (harmonicSystem z).largeValue θ →
        θ * (harmonicSystem z).size ≤ Real.log (8 * Real.log |u| + 39) + poleConst) ∧
      (∀ {θ T : ℝ}, 0 < θ → ∀ᶠ z : ℕ in atTop, ∀ u, 8 ≤ |u| → |u| ≤ T →
        u ∉ (harmonicSystem z).largeValue θ) :=
  ⟨fun hθ hS hA => S.sum_sum_column_ge hθ hS hA, fun hr ht hu => S.sub_mem_bohr hr ht hu,
    fun hz hu h => le_log_of_mem_largeValue hz hu h, fun hθ => eventually_not_mem_largeValue hθ⟩

/-- **Question 1, on boxes and rotations.** Every window of length `exp(10 y √(log y · log log y/δ))` enters every box on the primes up to `y`. Against every rotation, the modulus of the critical column stays below
its size by a negative power of `log |t|`, the saving away from the primes dividing `q` grows like `√P` when `q` contains every prime up to `P`, and more than `d` primes up to `L^{9d + 6}` are misaligned at precision `L^{−(9d + 10)}`. -/
theorem question_one_boxes_and_rotations {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ∀ (θ : ℕ → ℝ) (T : ℝ),
      ∃ t ∈ Set.Icc T (T + Real.exp (10 * y * √(Real.log y * Real.log (Real.log y) / δ))),
        ∀ q ∈ primesUpTo y, 1 - δ < bump (t * Real.log q - θ q)) ∧
      (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
        10 ^ 9 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 4 < N →
        ‖∑ p ∈ N.primesBelow, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))‖ ≤
          (∑ p ∈ N.primesBelow, 1 / √(p : ℝ)) -
            1 / (10 ^ 25 * Real.log |t| ^ 19 * Real.log (Real.log |t|) ^ 14)) ∧
      (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ q K P : ℕ, 1 ≤ q → 1 ≤ P →
        (∀ p : ℕ, p.Prime → p ≤ P → p ∣ q) →
        48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ K →
        4 * √(P : ℝ) *
            ((q.totient : ℝ) / q / (100000 * Real.log |t| ^ 4 * Real.log (Real.log |t|) ^ 2)) ^ 2 ≤
          ∑ p ∈ coprimePrimes q (q * K), (1 - Real.cos (t * Real.log p)) / √(p : ℝ)) ∧
      ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ Ex : Finset ℕ, (Ex.card : ℝ) ≤ Real.log |t| →
        ∃ p : ℕ, p.Prime ∧ p ∉ Ex ∧ (p : ℝ) ≤ Real.log |t| ^ (9 * Ex.card) * Real.log |t| ^ 6 ∧
          1 / (Real.log |t| ^ (9 * Ex.card) * Real.log |t| ^ 10) < phaseDist t p :=
  ⟨eventually_exists_mem_box_sharp hδ0 hδ1, norm_sum_primes_le, le_sum_primes_critical_coprime_of_large,
    exists_prime_not_mem_of_large⟩

open Classical in
/-- **Question 2, past the diagonal.** At weights `r^{−σ}` the energy is bounded at every `k` and `H`, and the oscillating energy of the critical column is bounded by the modulus, which stays below size. -/
theorem question_two_past_the_diagonal {Q : Finset ℕ} (hQ : ∀ r ∈ Q, r.Prime) {σ : ℝ} (hσ : 0 ≤ σ)
    (ha : ∀ r ∈ Q, 0 ≤ powWeight σ r) (k : ℕ) {H : ℝ} (hH : 0 < H) :
    (primeSystem Q (powWeight σ) ha).energy k H ≤
      k.factorial * (∑ r ∈ Q, powWeight σ r ^ 2) ^ k +
        24 * k.factorial * (∑ r ∈ Q, (r : ℝ) ^ (1 - 2 * σ)) ^ k / H +
        32 * (∑ r ∈ Q, powWeight σ r) ^ (2 * k) / H ^ 2 :=
  energy_le_past_diagonal hQ hσ ha k hH

/-- **Question 4, for the Ξ-current.** For `σ > 1` the current `2 Re(ξ' conj ξ)` is the restriction to the orbit of `𝒥_σ(t, ω) = 2|ξ|²(B − Σ_n Λ(n) n^{−σ} Re ω(n))`, whose worst point on every fibre is the pole, so `𝒥_σ` is nonnegative on the fibre over `t` exactly when the base pays `−ζ'/ζ(σ)`. -/
theorem question_four_xi_current {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    xiCurrent ⟨σ, t⟩ = xiLift σ t (orbitPoint t) ∧
      ((∀ ω : ℕ → ℂ, (∀ n, ‖ω n‖ ≤ 1) → 0 ≤ xiLift σ t ω) ↔
        -(deriv riemannZeta σ / riemannZeta σ).re ≤ xiBase ⟨σ, t⟩) := by
  rw [← lamColumn_pole_eq hσ]
  exact ⟨xiCurrent_eq_xiLift hσ t, xiLift_nonneg_iff hσ t⟩

/-- **Question 4, with coordinates that see the height.** The function `E(s)/(s + 3)` has no decomposition in the returning coordinates, and it has one in coordinates that do not return. -/
theorem question_four_height_coordinates :
    IsEmpty (AglerDecompositionAll eulerTestS eulerTestG) ∧
      (∀ n s, ‖heightCoord n s‖ ≤ 1) ∧
      (∀ p : ℕ, p.Prime → ∀ s, Tendsto (fun τ => heightCoord p (vshift' s τ)) atTop (𝓝 0)) ∧
      ∀ x y : Plane 2, HasSum (fun n => (1 - heightCoord n x * starRingEnd ℂ (heightCoord n y)) *
        ((∏ m ∈ Finset.range n, heightCoord m x) * starRingEnd ℂ (∏ m ∈ Finset.range n, heightCoord m y)))
        (1 - eulerTestS x * starRingEnd ℂ (eulerTestS y)) :=
  ⟨euler_test.2.2, euler_test_has_height_certificate.1, euler_test_has_height_certificate.2.1,
    euler_test_has_height_certificate.2.2.2⟩

end

end GaloisForLFunctions.PrimeTorusTheory
