import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Cofinal Sonin transport of the complete Euler source

The existing moving-shell theorem controls one orthonormal shell at a time.
That is not enough for the CCM source: the Euler tangent is one arbitrary
infinite `ell²` vector.

This file proves the missing uniform passage.  If moving isometric embeddings
converge after a fixed bounded operator on every coordinate vector, then they
converge on every `ell²` vector.  Applied to shifted exterior Sonin shells, it
gives one cofinal isometric embedding of the complete infinite source on which

* the central Sonin projection tends strongly to the identity; and
* the projected dilation corner tends strongly to an interior-shell isometry.

The result is then composed with the exact positive-integer and
squarefree-times-square Euler unitaries.  Thus no finite-rank truncation and no
source-energy loss remain between the global Euler carrier and the Sonin
corner.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- **Moving-isometry strong transport law.**  Coordinatewise convergence of
a uniformly bounded transport between moving isometric `ell²` embeddings
upgrades to convergence on every infinite source vector. -/
theorem cofinalOrthonormalEmbedding_strong_transport
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (B : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] K)
    (T : H →L[ℂ] K)
    (hbasis : ∀ i : ℕ, Tendsto (fun N =>
      T (A N (lp.single 2 i 1)) - B N (lp.single 2 i 1))
      atTop (𝓝 0))
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N => ‖T (A N x) - B N x‖) atTop (𝓝 0) := by
  let e : ℕ → lp (fun _ : ℕ => ℂ) 2 := fun i => lp.single 2 i 1
  have hfinite (m : ℕ) :
      Tendsto (fun N =>
        T (A N (∑ i ∈ Finset.range m, lp.single 2 i (x i))) -
          B N (∑ i ∈ Finset.range m, lp.single 2 i (x i)))
        atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.range m)
      (f := fun i N => (x i) • (T (A N (e i)) - B N (e i)))
      (a := fun _ => 0)
      (fun i _ => by
        simpa [e] using (hbasis i).const_smul (x i))
    simp only [Finset.sum_const_zero] at hsum
    convert hsum using 1
    funext N
    rw [map_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hsingle :
        lp.single 2 i (x i) = (x i) • e i := by
      ext j
      by_cases hij : i = j
      · subst j
        simp [e]
      · simp [e, hij]
    rw [hsingle, map_smul, map_smul, map_smul, smul_sub]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hden : 0 < 2 * (‖T‖ + 1) := by positivity
  have hpartial :
      Tendsto
        (fun m => ∑ i ∈ Finset.range m, lp.single 2 i (x i))
        atTop (𝓝 x) :=
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x).tendsto_sum_nat
  have hevent :
      ∀ᶠ m in atTop,
        ‖x - ∑ i ∈ Finset.range m, lp.single 2 i (x i)‖ <
          ε / (2 * (‖T‖ + 1)) := by
    have hball := hpartial.eventually
      (Metric.ball_mem_nhds x (div_pos hε hden))
    filter_upwards [hball] with m hm
    simpa [dist_eq_norm, norm_sub_rev] using hm
  obtain ⟨m, hm⟩ := eventually_atTop.1 hevent
  let y : lp (fun _ : ℕ => ℂ) 2 :=
    ∑ i ∈ Finset.range m, lp.single 2 i (x i)
  have hxy : ‖x - y‖ < ε / (2 * (‖T‖ + 1)) := hm m le_rfl
  have hy := hfinite m
  have hyEvent :
      ∀ᶠ N in atTop, ‖T (A N y) - B N y‖ < ε / 2 := by
    have hball := hy.eventually (Metric.ball_mem_nhds 0 (half_pos hε))
    filter_upwards [hball] with N hN
    simpa [y, dist_eq_norm] using hN
  apply eventually_atTop.1
  filter_upwards [hyEvent] with N hNy
  rw [Real.dist_eq]
  have htail :
      ‖T (A N (x - y)) - B N (x - y)‖ < ε / 2 := by
    calc
      ‖T (A N (x - y)) - B N (x - y)‖ ≤
          ‖T (A N (x - y))‖ + ‖B N (x - y)‖ := norm_sub_le _ _
      _ ≤ ‖T‖ * ‖A N (x - y)‖ + ‖B N (x - y)‖ :=
        add_le_add (T.le_opNorm _) le_rfl
      _ = (‖T‖ + 1) * ‖x - y‖ := by
        rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
        ring
      _ < (‖T‖ + 1) * (ε / (2 * (‖T‖ + 1))) :=
        mul_lt_mul_of_pos_left hxy (by positivity)
      _ = ε / 2 := by
        field_simp
  have hsplit :
      T (A N x) - B N x =
        (T (A N (x - y)) - B N (x - y)) +
          (T (A N y) - B N y) := by
    rw [← sub_add_cancel x y]
    simp
    module
  rw [hsplit]
  calc
    |‖(T (A N (x - y)) - B N (x - y)) +
        (T (A N y) - B N y)‖ - 0| =
      ‖(T (A N (x - y)) - B N (x - y)) +
        (T (A N y) - B N y)‖ := by simp
    _ ≤ ‖T (A N (x - y)) - B N (x - y)‖ +
        ‖T (A N y) - B N y‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add htail hNy
    _ = ε := by ring

/-- Shifted exterior shells used as the cofinal source frame. -/
def cofinalInverseDilatedEvenShell
    (c d r : ℝ) (hcd : c < d) (hr : 1 < r) (N n : ℕ) : SoninL2 :=
  inverseDilatedEvenShell c d r hcd hr (N + n)

theorem cofinalInverseDilatedEvenShell_orthonormal
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    Orthonormal ℂ (cofinalInverseDilatedEvenShell c d r hcd hr N) := by
  exact (inverseDilatedEvenShell_orthonormal c d r hc hcd hr).comp
    (fun n => N + n) (by intro i j h; exact Nat.add_left_cancel h)

/-- Isometric embedding of the complete countable source into a shifted
exterior Sonin shell frame. -/
def cofinalInverseDilatedShellEmbedding
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] SoninL2 :=
  (cofinalInverseDilatedEvenShell_orthonormal
    c d r hc hcd hr N).orthogonalFamily.linearIsometry

/-- Shifted interior shells carrying the output of the dilation corner. -/
def cofinalEvenShell
    (c d : ℝ) (hcd : c < d) (N n : ℕ) : SoninL2 :=
  evenShellVector c d hcd (N + n)

theorem cofinalEvenShell_orthonormal
    (c d : ℝ) (hc : 0 < c) (hcd : c < d) (N : ℕ) :
    Orthonormal ℂ (cofinalEvenShell c d hcd N) := by
  exact (evenShellVector_orthonormal c d hc hcd).comp
    (fun n => N + n) (by intro i j h; exact Nat.add_left_cancel h)

/-- Isometric embedding into the matching shifted interior shell frame. -/
def cofinalEvenShellEmbedding
    (c d : ℝ) (hc : 0 < c) (hcd : c < d) (N : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] SoninL2 :=
  (cofinalEvenShell_orthonormal c d hc hcd N).orthogonalFamily.linearIsometry

@[simp] theorem cofinalInverseDilatedShellEmbedding_single
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (N n : ℕ) (z : ℂ) :
    cofinalInverseDilatedShellEmbedding c d r hc hcd hr N
        (lp.single 2 n z) =
      z • cofinalInverseDilatedEvenShell c d r hcd hr N n := by
  rw [cofinalInverseDilatedShellEmbedding,
    OrthogonalFamily.linearIsometry_apply_single]
  rfl

@[simp] theorem cofinalEvenShellEmbedding_single
    (c d : ℝ) (hc : 0 < c) (hcd : c < d)
    (N n : ℕ) (z : ℂ) :
    cofinalEvenShellEmbedding c d hc hcd N (lp.single 2 n z) =
      z • cofinalEvenShell c d hcd N n := by
  rw [cofinalEvenShellEmbedding,
    OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- **Global cofinal Sonin projection law.**  The central Sonin projection is
asymptotically the identity on one moving isometric copy of every countable
`ell²` source, not only on individual shell vectors. -/
theorem centralSoninProjection_cofinalEmbedding_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hr : 1 < r) (harc : a < r * c)
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N =>
      ‖centralSoninProjection a
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x) -
        cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x‖)
      atTop (𝓝 0) := by
  apply cofinalOrthonormalEmbedding_strong_transport
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (T := centralSoninProjection a)
  intro i
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [cofinalInverseDilatedEvenShell] using
    (centralSoninProjection_inverseDilatedEvenShell_tendsto
      a c d r ha hc hcd hr harc).comp (tendsto_add_atTop_nat i)

/-- **Global cofinal Sonin dilation-corner law.**  The actual projected
dilation corner transports the complete infinite exterior source to the
matching interior isometric source with vanishing norm error. -/
theorem centralSoninDilationCorner_cofinalEmbedding_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
          centralSoninProjection a)
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x) -
        cofinalEvenShellEmbedding c d hc hcd N x‖) atTop (𝓝 0) := by
  apply cofinalOrthonormalEmbedding_strong_transport
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a)
  intro i
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using
    (centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
      a c d r ha hc hcd hda hr harc).comp (tendsto_add_atTop_nat i)

/-- Canonical positive-integer source reindexing used before the cofinal
Sonin shell embedding. -/
def eulerPositiveNatUnitary :
    EulerPositiveL2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpReindexEquiv Equiv.pnatEquivNat

/-- One cofinal Sonin embedding of the complete positive-integer Euler source. -/
def cofinalEulerPositiveSoninEmbedding
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    EulerPositiveL2 →ₗᵢ[ℂ] SoninL2 :=
  (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N).comp
    eulerPositiveNatUnitary.toLinearIsometry

/-- One cofinal Sonin embedding after the exact
`n = m² d` squarefree-times-square unitary. -/
def cofinalDyadicSquarefreeSoninEmbedding
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    DyadicSquarefreeL2 →ₗᵢ[ℂ] SoninL2 :=
  (cofinalEulerPositiveSoninEmbedding c d r hc hcd hr N).comp
    dyadicSquarefreeSquareUnitary.symm.toLinearIsometry

/-- The full positive-integer Euler source passes through the central Sonin
projection without asymptotic loss. -/
theorem centralSoninProjection_cofinalEulerPositive_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hr : 1 < r) (harc : a < r * c) (x : EulerPositiveL2) :
    Tendsto (fun N =>
      ‖centralSoninProjection a
          (cofinalEulerPositiveSoninEmbedding c d r hc hcd hr N x) -
        cofinalEulerPositiveSoninEmbedding c d r hc hcd hr N x‖)
      atTop (𝓝 0) := by
  simpa [cofinalEulerPositiveSoninEmbedding] using
    centralSoninProjection_cofinalEmbedding_tendsto
      a c d r ha hc hcd hr harc (eulerPositiveNatUnitary x)

/-- The complete squarefree-times-square Euler source passes through the
central Sonin projection without asymptotic loss. -/
theorem centralSoninProjection_cofinalDyadicSquarefree_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hr : 1 < r) (harc : a < r * c) (x : DyadicSquarefreeL2) :
    Tendsto (fun N =>
      ‖centralSoninProjection a
          (cofinalDyadicSquarefreeSoninEmbedding c d r hc hcd hr N x) -
        cofinalDyadicSquarefreeSoninEmbedding c d r hc hcd hr N x‖)
      atTop (𝓝 0) := by
  simpa [cofinalDyadicSquarefreeSoninEmbedding,
    cofinalEulerPositiveSoninEmbedding] using
    centralSoninProjection_cofinalEmbedding_tendsto
      a c d r ha hc hcd hr harc
        (eulerPositiveNatUnitary (dyadicSquarefreeSquareUnitary.symm x))

/-! ## Singular-scale diagonal selection -/

/-- **Singular diagonal transport law.**  Coordinatewise convergence of a
uniformly bounded transport on moving isometric `ell²` embeddings is strong
enough to follow an arbitrary moving source vector through an arbitrary
vanishing positive scale.

More precisely, one can choose a strictly increasing shell depth so that the
transport error divided by the prescribed scale tends to zero.  The selected
transport remains the original bounded operator; no inverse, scalar blow-up,
compactness, or uniform bound on the moving vectors is used. -/
theorem exists_strictMono_singularDiagonal_transport
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (B : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] K)
    (T : H →L[ℂ] K)
    (hbasis : ∀ i : ℕ, Tendsto (fun N =>
      T (A N (lp.single 2 i 1)) - B N (lp.single 2 i 1))
      atTop (𝓝 0))
    (x : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖T (A (depth n) (x n)) - B (depth n) (x n)‖ / epsilon n)
        atTop (𝓝 0) := by
  have hthreshold : ∀ n : ℕ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ‖T (A N (x n)) - B N (x n)‖ ≤ epsilon n ^ 2 := by
    intro n
    have hconv :=
      cofinalOrthonormalEmbedding_strong_transport A B T hbasis (x n)
    have hepsSq : 0 < epsilon n ^ 2 := sq_pos_of_pos (hepsilon n)
    have hevent :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (x n)) - B N (x n)‖ < epsilon n ^ 2 := by
      have hball := hconv.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hepsSq)
      filter_upwards [hball] with N hN
      simpa [Real.dist_eq] using hN
    obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
    exact ⟨M, fun N hMN => (hM N hMN).le⟩
  choose threshold hthresholdBound using hthreshold
  let depth : ℕ → ℕ :=
    fun n => n + ∑ k ∈ Finset.range (n + 1), threshold k
  have hdepthThreshold (n : ℕ) : threshold n ≤ depth n := by
    simp only [depth, Finset.sum_range_succ]
    omega
  have hdepthMono : StrictMono depth := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [depth, Finset.sum_range_succ]
    omega
  refine ⟨depth, hdepthMono, ?_⟩
  have hnonneg : ∀ n : ℕ,
      0 ≤ ‖T (A (depth n) (x n)) - B (depth n) (x n)‖ /
        epsilon n := by
    intro n
    exact div_nonneg (norm_nonneg _) (hepsilon n).le
  have hupper : ∀ n : ℕ,
      ‖T (A (depth n) (x n)) - B (depth n) (x n)‖ /
          epsilon n ≤ epsilon n := by
    intro n
    rw [div_le_iff₀ (hepsilon n)]
    have hbound :=
      hthresholdBound n (depth n) (hdepthThreshold n)
    nlinarith
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonneg)
    (Filter.Eventually.of_forall hupper)
    hepsilonZero

/-- **Two-jet singular diagonal law.**  One common strictly cofinal shell
schedule transports two arbitrary moving vectors through the same vanishing
scale.  This simultaneous form preserves their off-diagonal polarization; it
is strictly stronger than choosing unrelated subsequences for the two
vectors. -/
theorem exists_strictMono_singularDiagonal_transport_pair
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (B : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] K)
    (T : H →L[ℂ] K)
    (hbasis : ∀ i : ℕ, Tendsto (fun N =>
      T (A N (lp.single 2 i 1)) - B N (lp.single 2 i 1))
      atTop (𝓝 0))
    (father detail : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖T (A (depth n) (father n)) - B (depth n) (father n)‖ /
          epsilon n) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖T (A (depth n) (detail n)) - B (depth n) (detail n)‖ /
          epsilon n) atTop (𝓝 0) := by
  have hthreshold : ∀ n : ℕ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ‖T (A N (father n)) - B N (father n)‖ ≤ epsilon n ^ 2 ∧
      ‖T (A N (detail n)) - B N (detail n)‖ ≤ epsilon n ^ 2 := by
    intro n
    have hfather :=
      cofinalOrthonormalEmbedding_strong_transport A B T hbasis (father n)
    have hdetail :=
      cofinalOrthonormalEmbedding_strong_transport A B T hbasis (detail n)
    have hepsSq : 0 < epsilon n ^ 2 := sq_pos_of_pos (hepsilon n)
    have hfatherEventually :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (father n)) - B N (father n)‖ < epsilon n ^ 2 := by
      have hball := hfather.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hepsSq)
      filter_upwards [hball] with N hN
      simpa [Real.dist_eq] using hN
    have hdetailEventually :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (detail n)) - B N (detail n)‖ < epsilon n ^ 2 := by
      have hball := hdetail.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hepsSq)
      filter_upwards [hball] with N hN
      simpa [Real.dist_eq] using hN
    have hboth :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (father n)) - B N (father n)‖ ≤ epsilon n ^ 2 ∧
          ‖T (A N (detail n)) - B N (detail n)‖ ≤ epsilon n ^ 2 := by
      filter_upwards [hfatherEventually, hdetailEventually] with N hF hD
      exact ⟨hF.le, hD.le⟩
    exact eventually_atTop.1 hboth
  choose threshold hthresholdBound using hthreshold
  let depth : ℕ → ℕ :=
    fun n => n + ∑ k ∈ Finset.range (n + 1), threshold k
  have hdepthThreshold (n : ℕ) : threshold n ≤ depth n := by
    simp only [depth, Finset.sum_range_succ]
    omega
  have hdepthMono : StrictMono depth := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [depth, Finset.sum_range_succ]
    omega
  refine ⟨depth, hdepthMono, ?_, ?_⟩
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (Filter.Eventually.of_forall fun n => ?_)
      hepsilonZero
    rw [div_le_iff₀ (hepsilon n)]
    have hbound :=
      (hthresholdBound n (depth n) (hdepthThreshold n)).1
    nlinarith
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (Filter.Eventually.of_forall fun n => ?_)
      hepsilonZero
    rw [div_le_iff₀ (hepsilon n)]
    have hbound :=
      (hthresholdBound n (depth n) (hdepthThreshold n)).2
    nlinarith

/-- **Singular codiagonal stability law.**  If both legs of an off-diagonal
pair are transported with `o(epsilon)` error and the two factors used in the
polarization stay uniformly bounded, then the transported codiagonal itself
has `o(epsilon)` error.  This is the nonlinear step needed to pass from
strong vector transport to a singularly rescaled Ward column. -/
theorem tendsto_inner_sub_inner_norm_div_zero
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (xFather yFather xDetail yDetail : ℕ → H)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (fatherBound detailBound : ℝ)
    (hyFather : ∀ n, ‖yFather n‖ ≤ fatherBound)
    (hxDetail : ∀ n, ‖xDetail n‖ ≤ detailBound)
    (hfatherError : Tendsto (fun n =>
      ‖xFather n - yFather n‖ / epsilon n) atTop (𝓝 0))
    (hdetailError : Tendsto (fun n =>
      ‖xDetail n - yDetail n‖ / epsilon n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ‖inner ℂ (xFather n) (xDetail n) -
          inner ℂ (yFather n) (yDetail n)‖ / epsilon n)
      atTop (𝓝 0) := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ ‖inner ℂ (xFather n) (xDetail n) -
          inner ℂ (yFather n) (yDetail n)‖ / epsilon n := by
    intro n
    exact div_nonneg (norm_nonneg _) (hepsilon n).le
  have hupper : ∀ n : ℕ,
      ‖inner ℂ (xFather n) (xDetail n) -
          inner ℂ (yFather n) (yDetail n)‖ / epsilon n ≤
        (‖xFather n - yFather n‖ / epsilon n) * detailBound +
          fatherBound * (‖xDetail n - yDetail n‖ / epsilon n) := by
    intro n
    have hdecomp :
        inner ℂ (xFather n) (xDetail n) -
            inner ℂ (yFather n) (yDetail n) =
          inner ℂ (xFather n - yFather n) (xDetail n) +
            inner ℂ (yFather n) (xDetail n - yDetail n) := by
      rw [inner_sub_left, inner_sub_right]
      abel
    rw [hdecomp]
    calc
      ‖inner ℂ (xFather n - yFather n) (xDetail n) +
          inner ℂ (yFather n) (xDetail n - yDetail n)‖ /
            epsilon n ≤
          (‖inner ℂ (xFather n - yFather n) (xDetail n)‖ +
            ‖inner ℂ (yFather n) (xDetail n - yDetail n)‖) /
              epsilon n := by
        exact div_le_div_of_nonneg_right
          (norm_add_le _ _) (hepsilon n).le
      _ ≤
          (‖xFather n - yFather n‖ * ‖xDetail n‖ +
            ‖yFather n‖ * ‖xDetail n - yDetail n‖) /
              epsilon n := by
        apply div_le_div_of_nonneg_right _ (hepsilon n).le
        exact add_le_add
          (norm_inner_le_norm _ _)
          (norm_inner_le_norm _ _)
      _ =
          (‖xFather n - yFather n‖ / epsilon n) * ‖xDetail n‖ +
            ‖yFather n‖ *
              (‖xDetail n - yDetail n‖ / epsilon n) := by
        field_simp [(hepsilon n).ne']
      _ ≤
          (‖xFather n - yFather n‖ / epsilon n) * detailBound +
            fatherBound *
              (‖xDetail n - yDetail n‖ / epsilon n) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hxDetail n)
            (div_nonneg (norm_nonneg _) (hepsilon n).le))
          (mul_le_mul_of_nonneg_right (hyFather n)
            (div_nonneg (norm_nonneg _) (hepsilon n).le))
  have hright : Tendsto (fun n =>
      (‖xFather n - yFather n‖ / epsilon n) * detailBound +
        fatherBound * (‖xDetail n - yDetail n‖ / epsilon n))
      atTop (𝓝 0) := by
    convert (hfatherError.mul_const detailBound).add
      (hdetailError.const_mul fatherBound) using 1
    simp
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonneg)
    (Filter.Eventually.of_forall hupper)
    hright

/-- **Two-jet singular codiagonal transport.**  One strictly cofinal schedule
simultaneously transports two arbitrary moving source vectors and their
off-diagonal inner product through the same vanishing scale.  No convergence
or uniform norm bound on either source vector is required: shell depth adapts
to the exact size of each moving two-jet. -/
theorem exists_strictMono_singularDiagonal_transport_pair_codiagonal
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (B : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] K)
    (T : H →L[ℂ] K)
    (hbasis : ∀ i : ℕ, Tendsto (fun N =>
      T (A N (lp.single 2 i 1)) - B N (lp.single 2 i 1))
      atTop (𝓝 0))
    (father detail : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖T (A (depth n) (father n)) - B (depth n) (father n)‖ /
          epsilon n) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖T (A (depth n) (detail n)) - B (depth n) (detail n)‖ /
          epsilon n) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖inner ℂ
              (T (A (depth n) (father n)))
              (T (A (depth n) (detail n))) -
            inner ℂ (father n) (detail n)‖ / epsilon n)
        atTop (𝓝 0) := by
  let scale : ℕ → ℝ := fun n =>
    epsilon n ^ 2 /
      (1 + ‖T‖ * ‖detail n‖ + ‖father n‖)
  have hdenPos (n : ℕ) :
      0 < 1 + ‖T‖ * ‖detail n‖ + ‖father n‖ := by positivity
  have hscalePos (n : ℕ) : 0 < scale n := by
    exact div_pos (sq_pos_of_pos (hepsilon n)) (hdenPos n)
  have hscaleLe (n : ℕ) : scale n ≤ epsilon n ^ 2 := by
    dsimp [scale]
    rw [div_le_iff₀ (hdenPos n)]
    have hnonneg :
        0 ≤ ‖T‖ * ‖detail n‖ + ‖father n‖ := by positivity
    nlinarith [sq_nonneg (epsilon n)]
  have hthreshold : ∀ n : ℕ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ‖T (A N (father n)) - B N (father n)‖ ≤ scale n ∧
      ‖T (A N (detail n)) - B N (detail n)‖ ≤ scale n := by
    intro n
    have hfather :=
      cofinalOrthonormalEmbedding_strong_transport A B T hbasis (father n)
    have hdetail :=
      cofinalOrthonormalEmbedding_strong_transport A B T hbasis (detail n)
    have hfatherEventually :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (father n)) - B N (father n)‖ < scale n := by
      have hball := hfather.eventually
        (Metric.ball_mem_nhds (0 : ℝ) (hscalePos n))
      filter_upwards [hball] with N hN
      simpa [Real.dist_eq] using hN
    have hdetailEventually :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (detail n)) - B N (detail n)‖ < scale n := by
      have hball := hdetail.eventually
        (Metric.ball_mem_nhds (0 : ℝ) (hscalePos n))
      filter_upwards [hball] with N hN
      simpa [Real.dist_eq] using hN
    have hboth :
        ∀ᶠ N : ℕ in atTop,
          ‖T (A N (father n)) - B N (father n)‖ ≤ scale n ∧
          ‖T (A N (detail n)) - B N (detail n)‖ ≤ scale n := by
      filter_upwards [hfatherEventually, hdetailEventually] with N hF hD
      exact ⟨hF.le, hD.le⟩
    exact eventually_atTop.1 hboth
  choose threshold hthresholdBound using hthreshold
  let depth : ℕ → ℕ :=
    fun n => n + ∑ k ∈ Finset.range (n + 1), threshold k
  have hdepthThreshold (n : ℕ) : threshold n ≤ depth n := by
    simp only [depth, Finset.sum_range_succ]
    omega
  have hdepthMono : StrictMono depth := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [depth, Finset.sum_range_succ]
    omega
  have hfatherAt (n : ℕ) :
      ‖T (A (depth n) (father n)) - B (depth n) (father n)‖ ≤
        scale n :=
    (hthresholdBound n (depth n) (hdepthThreshold n)).1
  have hdetailAt (n : ℕ) :
      ‖T (A (depth n) (detail n)) - B (depth n) (detail n)‖ ≤
        scale n :=
    (hthresholdBound n (depth n) (hdepthThreshold n)).2
  refine ⟨depth, hdepthMono, ?_, ?_, ?_⟩
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (Filter.Eventually.of_forall fun n => ?_)
      hepsilonZero
    rw [div_le_iff₀ (hepsilon n)]
    simpa only [pow_two] using (hfatherAt n).trans (hscaleLe n)
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (Filter.Eventually.of_forall fun n => ?_)
      hepsilonZero
    rw [div_le_iff₀ (hepsilon n)]
    simpa only [pow_two] using (hdetailAt n).trans (hscaleLe n)
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (Filter.Eventually.of_forall fun n => ?_)
      hepsilonZero
    rw [div_le_iff₀ (hepsilon n)]
    have hdecomp :
        inner ℂ
              (T (A (depth n) (father n)))
              (T (A (depth n) (detail n))) -
            inner ℂ (father n) (detail n) =
          inner ℂ
              (T (A (depth n) (father n)) -
                B (depth n) (father n))
              (T (A (depth n) (detail n))) +
            inner ℂ (B (depth n) (father n))
              (T (A (depth n) (detail n)) -
                B (depth n) (detail n)) := by
      rw [← (B (depth n)).inner_map_map (father n) (detail n),
        inner_sub_left, inner_sub_right]
      abel
    rw [hdecomp]
    calc
      ‖inner ℂ
            (T (A (depth n) (father n)) -
              B (depth n) (father n))
            (T (A (depth n) (detail n))) +
          inner ℂ (B (depth n) (father n))
            (T (A (depth n) (detail n)) -
              B (depth n) (detail n))‖ ≤
          ‖T (A (depth n) (father n)) -
              B (depth n) (father n)‖ *
              ‖T (A (depth n) (detail n))‖ +
            ‖B (depth n) (father n)‖ *
              ‖T (A (depth n) (detail n)) -
                B (depth n) (detail n)‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ scale n * (‖T‖ * ‖detail n‖) +
            ‖father n‖ * scale n := by
        exact add_le_add
          (mul_le_mul (hfatherAt n)
            (by
              calc
                ‖T (A (depth n) (detail n))‖ ≤
                    ‖T‖ * ‖A (depth n) (detail n)‖ := T.le_opNorm _
                _ = ‖T‖ * ‖detail n‖ := by
                  rw [LinearIsometry.norm_map])
            (norm_nonneg _)
            (hscalePos n).le)
          (by
            rw [LinearIsometry.norm_map]
            exact mul_le_mul_of_nonneg_left
              (hdetailAt n) (norm_nonneg _))
      _ = scale n *
          (‖T‖ * ‖detail n‖ + ‖father n‖) := by ring
      _ ≤ epsilon n * epsilon n := by
        dsimp [scale]
        field_simp [(hdenPos n).ne']
        nlinarith [sq_nonneg (epsilon n),
          mul_nonneg (norm_nonneg T) (norm_nonneg (detail n)),
          norm_nonneg (father n)]

/-- **Finite-packet singular diagonal law.**  Every finite moving packet is
transported through one common strictly cofinal shell schedule with
`o(epsilon)` error in every channel.  Hence all packet Gram entries and
codiagonals survive the singular quotient simultaneously. -/
theorem exists_strictMono_singularDiagonal_transport_finite
    {H K ι : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (B : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] K)
    (T : H →L[ℂ] K)
    (hbasis : ∀ i : ℕ, Tendsto (fun N =>
      T (A N (lp.single 2 i 1)) - B N (lp.single 2 i 1))
      atTop (𝓝 0))
    (packet : ℕ → ι → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      ∀ i : ι, Tendsto (fun n =>
        ‖T (A (depth n) (packet n i)) -
            B (depth n) (packet n i)‖ / epsilon n)
        atTop (𝓝 0) := by
  have hthreshold : ∀ n : ℕ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ∀ i : ι,
        ‖T (A N (packet n i)) - B N (packet n i)‖ ≤ epsilon n ^ 2 := by
    intro n
    have hepsSq : 0 < epsilon n ^ 2 := sq_pos_of_pos (hepsilon n)
    have hevent : ∀ᶠ N : ℕ in atTop, ∀ i : ι,
        ‖T (A N (packet n i)) - B N (packet n i)‖ ≤ epsilon n ^ 2 := by
      rw [Filter.eventually_all]
      intro i
      have hconv :=
        cofinalOrthonormalEmbedding_strong_transport
          A B T hbasis (packet n i)
      have hball := hconv.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hepsSq)
      filter_upwards [hball] with N hN
      exact (by simpa [Real.dist_eq] using hN : _ < _).le
    exact eventually_atTop.1 hevent
  choose threshold hthresholdBound using hthreshold
  let depth : ℕ → ℕ :=
    fun n => n + ∑ k ∈ Finset.range (n + 1), threshold k
  have hdepthThreshold (n : ℕ) : threshold n ≤ depth n := by
    simp only [depth, Finset.sum_range_succ]
    omega
  have hdepthMono : StrictMono depth := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [depth, Finset.sum_range_succ]
    omega
  refine ⟨depth, hdepthMono, ?_⟩
  intro i
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (norm_nonneg _) (hepsilon n).le)
    (Filter.Eventually.of_forall fun n => ?_)
    hepsilonZero
  rw [div_le_iff₀ (hepsilon n)]
  have hbound :=
    hthresholdBound n (depth n) (hdepthThreshold n) i
  nlinarith

/-- The central Sonin projection can follow any moving `ell²` source through
any vanishing singular scale after a source-independent cofinal choice of
shell depth.  In particular, division by the Euler normal parameter does not
destroy the projection limit. -/
theorem exists_centralSoninProjection_singularDiagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hr : 1 < r) (harc : a < r * c)
    (x : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖centralSoninProjection a
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (x n)) -
            cofinalInverseDilatedShellEmbedding
              c d r hc hcd hr (depth n) (x n)‖ /
          epsilon n)
        atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (T := centralSoninProjection a)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell] using
        (centralSoninProjection_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hr harc).comp (tendsto_add_atTop_nat i))
    (x := x) (epsilon := epsilon) hepsilon hepsilonZero

/-- The projected Sonin dilation corner admits the same singular diagonal
selection.  Thus the non-diagonal corner, not merely the central projection,
can transport arbitrary moving source graph vectors with error
`o(epsilon)`. -/
theorem exists_centralSoninDilationCorner_singularDiagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
              centralSoninProjection a)
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (x n)) -
            cofinalEvenShellEmbedding c d hc hcd (depth n) (x n)‖ /
          epsilon n)
        atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using
        (centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hda hr harc).comp
            (tendsto_add_atTop_nat i))
    (x := x) (epsilon := epsilon) hepsilon hepsilonZero

/-- **Source father/detail singular Sonin law.**  One common moving Sonin
corner transports both legs of an arbitrary moving source two-jet with
relative error `o(epsilon)`.  Consequently the father/detail codiagonal is
retained through the singular Euler quotient; the construction never
scalarizes either leg. -/
theorem exists_centralSoninDilationCorner_singularDiagonal_pair
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (father detail : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
              centralSoninProjection a)
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (father n)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (father n)‖ /
          epsilon n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
              centralSoninProjection a)
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (detail n)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (detail n)‖ /
          epsilon n)
        atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport_pair
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using
        (centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hda hr harc).comp
            (tendsto_add_atTop_nat i))
    (father := father) (detail := detail)
    (epsilon := epsilon) hepsilon hepsilonZero

/-- **Singular Sonin codiagonal law.**  The actual non-diagonal projected
dilation corner preserves the father/detail codiagonal to `o(epsilon)` along
one strictly cofinal shell schedule.  This upgrades vector-level carrier
survival to the off-diagonal scalar needed by a Ward column. -/
theorem exists_centralSoninDilationCorner_singularDiagonal_pair_codiagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (father detail : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
              centralSoninProjection a)
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (father n)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (father n)‖ /
          epsilon n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
              centralSoninProjection a)
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (detail n)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (detail n)‖ /
          epsilon n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖inner ℂ
              ((crossBoundary (centralSoninProjection a)
                    (dilationSum r hr) ∘L centralSoninProjection a)
                (cofinalInverseDilatedShellEmbedding
                  c d r hc hcd hr (depth n) (father n)))
              ((crossBoundary (centralSoninProjection a)
                    (dilationSum r hr) ∘L centralSoninProjection a)
                (cofinalInverseDilatedShellEmbedding
                  c d r hc hcd hr (depth n) (detail n))) -
            inner ℂ (father n) (detail n)‖ / epsilon n)
        atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport_pair_codiagonal
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using
        (centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hda hr harc).comp
            (tendsto_add_atTop_nat i))
    (father := father) (detail := detail)
    (epsilon := epsilon) hepsilon hepsilonZero

/-- **Finite-packet singular Sonin incidence.**  The actual non-diagonal
Sonin dilation corner transports every finite moving Euler packet through
one common shell schedule with error negligible after division by the Euler
normal scale. -/
theorem exists_centralSoninDilationCorner_singularDiagonal_finite
    {ι : Type*} [Fintype ι]
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (packet : ℕ → ι → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      ∀ i : ι, Tendsto (fun n =>
        ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
              centralSoninProjection a)
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (packet n i)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (packet n i)‖ /
          epsilon n)
        atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport_finite
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using
        (centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hda hr harc).comp
            (tendsto_add_atTop_nat i))
    (packet := packet) (epsilon := epsilon) hepsilon hepsilonZero

end RHTower
