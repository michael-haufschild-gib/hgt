import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCountertermRankDichotomy
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ThePoleNodeCompletesTheArchimedeanGerm
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.IntegerThetaPrefixesReadTheDefectWithoutLoss
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheGaugeChargeOfACoupling
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.LogCellsFixTheGauge
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.CriticalDiscsAndTheTerminalLens
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.PositivityIsIrreversible
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.CollectivePacketsDiluteOverIndependentOrdinates
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheRamanujanTwinsSurviveExactlyOnPerOrderRelations
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCellHolonomyDefectCountsChargedCells
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.HarnackOnTheCaratheodoryRegion

/-!
# The laws of Renormalized Biarithmetic Geometry

One statement collecting the laws proved in the programme:

1. **Self-energy survival.** A periodic Abel germ keeps positivity exactly on the linear relations
   among its modes. Every renormalization of the prime-place torsion germ has trivial
   survival cone and the renormalized limit is indefinite at every prime power; every
   renormalization of the archimedean lattice germ has the polar-neutral hyperplane as survival
   cone, where the digamma Hankel form is positive; the pole node completes it to the positive
   harmonic-number kernel.
2. **Lossless amplification.** A positive Hecke defect amplifies dyadically with loss `D(f)`, and RH
   is sub-doubly-exponential dyadic growth of every Hecke defect.
3. **Gauge charge.** A coupling is blind under every real sign gauge iff it is of square class;
   successor couplings are charged.
4. **Cells fix the gauge.** The dyadic cell dilation is covariant only at the Euler gauge.
5. **Terminal lens.** The lens of a terminal is zero-free away from the terminal, and the outward
   floor of `Re ξ′/ξ` spreads to discs about the ray.
6. **Irreversibility.** A nontrivial positive deformation cannot be undone.
7. **Height law.** A positive packet on a cloud of nonnegative integer combinations of independent
   generators, with heights `≤ M`, buys at most `M` times its pole share.
8. **Quantitative cell holonomy.** At the Liouville gauge the minimal cell covariance defect lies
   between `2N₊` and `4N₊`, `N₊ = #{a ≤ X : λ(a) = λ(2a + 1)}`.
9. **Ramanujan orthogonality.** Ramanujan modes of different orders are orthogonal over a common
   period, so twins survive exactly on per-order relations.
-/

noncomputable section

open Filter Topology Finset RHTower

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open Zeta23 GaloisForLFunctions.ConjugateDiagonalGeometry GaloisForLFunctions.ArithmeticPolarization
  BiarithmeticGaugeGeometry ArithmeticCorrespondencePositivity

/-- **The laws of Renormalized Biarithmetic Geometry.** -/
theorem renormalized_biarithmetic_geometry_laws :
    -- Self-energy survival: periodic germs keep positivity on the relations among their modes
    (∀ (n : ℕ) (a : Fin n → ℕ → ℝ) (q : ℕ), 0 < q → (∀ α, Function.Periodic (a α) q) →
      ∀ (x : Fin n → ℝ), (∀ α, 0 ≤ x α) →
        ∃ A : Matrix (Fin n) (Fin n) ℝ,
          (∀ α β, Tendsto (fun r => periodicGerm a x r α β -
            (-Real.log (1 - r)) * cesaroGram a q α β) (𝓝[<] 1) (𝓝 (A α β))) ∧
          ∀ C : Fin n → ℝ, (∀ k, ∑ α, C α * a α k = 0) → 0 ≤ quad A C) ∧
    -- Self-energy survival: prime place
    (∀ (S : Finset ℕ), (∀ n ∈ S, 0 < n) → S.Nonempty →
      ∀ (t : ℝ → ℝ) (C A' : Matrix S S ℝ),
        (∀ i j, Tendsto (fun r => torsionGerm S r i j - t r * C i j) (𝓝[<] 1) (𝓝 (A' i j))) →
          survivalCone C = {0}) ∧
    (∀ q : ℕ, IsPrimePow q → ∃ x : ℕ → ℝ, torsionLimitForm {1, q} x < 0) ∧
    -- Self-energy survival: archimedean place and the pole node
    (∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 < x i) → ∀ c : Fin n → ℝ, ∑ i, c i = 0 →
      0 ≤ ∑ i, ∑ j, c i * c j * (-(Complex.digamma ((x i + x j : ℝ) : ℂ)).re)) ∧
    (∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 ≤ x i) → ∀ c : Fin n → ℝ,
      0 ≤ ∑ i, ∑ j, c i * c j * (harmonicFn (x i) + harmonicFn (x j) - harmonicFn (x i + x j))) ∧
    -- Lossless amplification
    (∀ (f : CompactTest) (L θ : ℝ), mass f * (2 * Real.cosh θ - 2) ≤ heckeDefect f L →
      ∀ k : ℕ, mass f * (2 * Real.cosh (2 ^ k * θ) - 2) ≤ heckeDefect f (2 ^ k * L)) ∧
    (RiemannHypothesis ↔ ∀ f : CompactTest, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
      heckeDefect f (2 ^ k) ≤ C * Real.exp (ε * 2 ^ k)) ∧
    -- Gauge charge
    (∀ {n a b : ℕ}, n ≠ 0 → a ≠ 0 → b ≠ 0 →
      ((∀ ω : PrimeGauge, IsRealSignGauge ω → ω.gaugeChar n = ω.gaugeChar a * ω.gaugeChar b) ↔
        IsSquare (n * a * b))) ∧
    (∀ {a : ℕ}, 0 < a →
      ∃ ω : PrimeGauge, IsRealSignGauge ω ∧ ω.gaugeChar a * ω.gaugeChar (a + 1) ≠ 1) ∧
    -- Cells fix the gauge
    (∀ ω : PrimeGauge, (∃ c : ℂ, ∀ q : ℕ → ℂ, q 0 = 0 →
      gaugeTwist ω (cellDilate 2 q) = c • cellDilate 2 (gaugeTwist ω q)) ↔
        ω = PrimeGauge.eulerGauge) ∧
    -- Terminal lens
    (∀ {p : XiZeroCopy}, IsTerminal p → 1 / 2 < (p.1 : ℂ).re → ∀ {s : ℂ}, InTerminalLens p s →
      |s.im - xiZeroHeight p| < lensWidth (xiZeroDepth p) → s ≠ (p.1 : ℂ) → xi s ≠ 0) ∧
    -- Irreversibility
    (∀ {Λ₀ Λ : ℂ → ℂ}, PositiveDeformation Λ₀ Λ →
      (∀ σ₂ : ℝ, ∃ σ : ℝ, σ₂ < σ ∧ logDeriv Λ₀ (σ : ℂ) ≠ logDeriv Λ (σ : ℂ)) →
        ¬ PositiveDeformation Λ Λ₀) ∧
    -- Kronecker dilution
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {ω : ι → ℝ}, LinearIndependent ℚ ω →
      ∀ (a₀ : ℝ) (a : ι → ℝ), (∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t)) →
        ∑ j, |a j| ≤ a₀) ∧
    -- The height law
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] {g : ι → ℝ},
      LinearIndependent ℚ g → ∀ (n : κ → ι → ℕ) (M : ℕ),
        (∀ j, 1 ≤ ∑ i, n j i ∧ ∑ i, n j i ≤ M) → ∀ (a₀ : ℝ) (a : κ → ℝ),
          (∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t)) →
            ∑ j, a j ≤ M * a₀) ∧
    -- Quantitative cell holonomy at the Liouville gauge
    (∀ X : ℕ, (∀ c : ℝ, 2 * ((liouvilleAgreements X).card : ℝ) ≤
        hsDefect PrimeGauge.liouvilleGauge X c) ∧
      hsDefect PrimeGauge.liouvilleGauge X ((-1 : ℝ) : ℂ) = 4 * (liouvilleAgreements X).card) ∧
    -- Ramanujan orthogonality
    (∀ {m n q : ℕ}, 0 < m → 0 < n → m ∣ q → n ∣ q →
      ∑ k ∈ range q, ramanujanMode m k * ramanujanMode n k =
        if m = n then (q : ℝ) * Nat.totient n else 0) ∧
    -- The outward floor spreads
    (∃ c : ℝ, 0 < c ∧ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re → IsTerminal p →
      ∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
        ∀ s : ℂ, ‖s - ((p.1 : ℂ) + h)‖ ≤ rayRadius (xiZeroDepth p) * h / 2 →
          (((xiZeroCopyFiber p.1).card : ℝ) / h +
            ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
            c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4)) / 3 ≤ (logDeriv xi s).re) :=
  ⟨fun _ a _ hq hper _ hx => periodicGerm_survival a hq hper hx,
    fun _ hS hne _ _ _ hC => torsion_survivalCone_eq hS hne hC,
    fun _ hq => torsionLimitForm_neg hq,
    fun _ _ hx _ hc => neg_digamma_hankel_nonneg hx hc,
    fun _ _ hx c => harmonicKernel_nonneg hx c,
    fun f L θ h k => heckeDefect_dyadic_ge f L θ h k,
    riemannHypothesis_iff_dyadic_subexp,
    fun hn ha hb => realSignBlind_iff_isSquare hn ha hb,
    fun ha => successor_coupling_charged ha,
    cellDilate_two_covariant_iff,
    fun hp hright _ hs hlt hsp => xi_ne_zero_of_mem_terminalLens hp hright hs hlt hsp,
    fun h hne => not_positiveDeformation_of_ne h hne,
    fun hind a₀ a hP => sum_abs_le_of_packet_nonneg hind a₀ a hP,
    fun hind n M hh a₀ a hP => sum_le_height_mul_of_generated_packet hind n M hh a₀ a hP,
    hsDefect_liouville_sandwich,
    fun hm hn hmq hnq => sum_ramanujanMode_mul hm hn hmq hnq,
    exists_terminal_floor_spreads⟩

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
