import GaloisForLFunctions.HyperbolicArakelovTheory.TheLeafAndHeckeSeparationOfTheAdelicCarrier
import GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledLocalProductObstructsOffDiagonalAndTorusInvariance
import GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledOrbitDensityMatchesTheArchimedeanConstants
import GaloisForLFunctions.HyperbolicArakelovTheory.TheGramCouplingOfTheGreenAndTorsionChannels
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsOffDiagonalIsContactsPlusJets

/-!
# Weil's diagonal is not the finite part of one glued carrier object

This file resolves Question **(G)** on the projective adelic carrier
`X = Γ \ (ℍ³ × Π'_p PGL₂(ℚ_p)/K_p)`, `Γ = J⁻¹ SL₂(ℚ) J`:

> Is there a normalization of the coupled orbit sum on `X`, invariant under the rational torus and
> determined by the Laplacian of `ℍ³` and the operators `A_p` alone, whose finite part is Weil's
> form as a bilinear pairing of the degree points — with off-diagonal given by the contacts of the
> arithmetic square plus the archimedean jets, and diagonal equal on packets to the
> Robin-normalized diagonal of the scattering tower, with no further counterterm?

**Answer: No.** While the three presentations exist separately — contacts plus jets in the
arithmetic square (`AbsoluteGeometryOfSpecZ.frobeniusIntersection_eq_tsum_jets_add_contacts`), a
torus-orbit finite part on the carrier (`CoupledOrbit.tendsto_orbit_finitePart`) whose smooth
density matches Weil's archimedean digamma constant (`ArchimedeanConstantBridge.four_mul_regularMean_eq`),
and the shift-invariant Robin-normalized packet functional on the modular scattering tower
(`ArchimedeanConstantBridge.tendsto_geometricWeilEnergy_shift_re_weilQuad`) — they cannot be
realized as one glued object on `X`:

1. **Constant-diagonal rigidity of torus-invariant local kernels
   (`local_invariant_torus_diagonal_const`).** Because `adelicDegreeShift n ∈ AdelicGroup` maps
   `x_1` to `x_n` and commutes in `AdelicGroup` with every rational torus element `γ_q`, *every*
   `AdelicGroup`-invariant kernel `K₀ : GlobalSpace → GlobalSpace → ℝ` and *every* torus-orbit
   renormalization functional `ℛ : (ℚˣ → ℝ) → ℝ` produces a degree-independent diagonal
   `B(n, n) = B(1, 1)`.
2. **Dyadic `-¼ N log N` divergence against the scale-invariant scattering tower
   (`dyadicNormalizedPairing_le_of_log_diag`, `tendsto_atBot_dyadicNormalizedPairing`,
   `not_exists_torus_invariant_local_glued_form`).** Every pairing `B : ℕ → ℕ → ℝ` matching
   `weilDeltaKernel` off the diagonal whose diagonal grows at most logarithmically
   (`B n n ≤ C (1 + log n)`, including all constant torus-invariant diagonals and all
   discriminant-size diagonals) satisfies
   `N⁻² ∑_{m,n ∈ [N, 2N)} √(mn) B(m, n) ≤ 2|C|(1 + log(2N)) + (17/4)N - (1/4)N log N → -∞`,
   whereas the Robin-normalized scattering tower on translated packets `F_N(u) = F₀(u - log N)` is
   identically constant `= weilQuad F₀`.
3. **Exact discriminant obstruction on smoothed/Gram-coupled packets
   (`gramLocked_sub_scatteringTower_eq_neg_discriminant`,
   `gramLocked_sub_scatteringTower_prime_cube_jump`).** On separated `C_c²` packets `f = atomicTest N x g`,
   the `r → 1⁻` limit of `gramLockedPacket` at the canonical archimedean constant
   `c = -4 * regularMean - (log(4π) + γ) = 2 * gammaHardyPhaseRate 0` minus the `M → ∞`
   scattering-tower limit equals `-(∫ g²) ∑_{n=1}^N x_n² selfIntersection n`. Moreover, for *every*
   scalar normalization `c ∈ ℝ` and every prime `p`, the discrepancy jumps between the unit-mass
   atoms at `p` and `p³` by `-2 (∫ g²) log p < 0`, so no scalar counterterm can eliminate the
   discriminant defect.
4. **Master synthesis (`refutation_of_glued_carrier_question_G`).** Combines the constant-diagonal
   no-go, dyadic divergence, off-diagonal prime-erasure and Pell non-decay of
   `adelicCriticalProduct`, bounded-place-rank Hecke vanishing, and the exact smoothed-packet
   discriminant jump into one unconditional obstruction theorem.
-/

set_option autoImplicit false
noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical

namespace GaloisForLFunctions.HyperbolicArakelovTheory.GluedCarrierNoGo

open FullAdelic AdelicAdjacency CarrierSeparation CoupledProductObstruction
open ArchimedeanConstantBridge CoupledOrbit ScatteringTower
open SurfaceOfSpecZ ArithmeticEffectivityTheory ArithmeticIntersectionTheory
open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-! ## 1. Constant-diagonal rigidity of torus-invariant local kernels -/

/-- **Constant-diagonal rigidity.** For *every* `AdelicGroup`-invariant two-point kernel
`K₀ : GlobalSpace → GlobalSpace → ℝ` (hence every kernel determined by the local `SL₂(ℂ)`-invariant
geometry of `ℍ³` and the local `PGL₂(ℚ_p)`-invariant tree operators `A_p`) and *every* rational-torus
orbit renormalization functional `ℛ : (ℚˣ → ℝ) → ℝ`, the diagonal pairing at degree `n` is
independent of `n`. -/
theorem local_invariant_torus_diagonal_const
    (K₀ : GlobalSpace → GlobalSpace → ℝ)
    (hK₀ : ∀ (g : AdelicGroup) (x y : GlobalSpace), K₀ (g • x) (g • y) = K₀ x y)
    (ℛ : (ℚˣ → ℝ) → ℝ) (n : ℕ+) :
    ℛ (fun q : ℚˣ => K₀ (originalDegreePoint n)
        ((torusElem q.val q.ne_zero : AdelicGroup) • originalDegreePoint n)) =
      ℛ (fun q : ℚˣ => K₀ (originalDegreePoint 1)
        ((torusElem q.val q.ne_zero : AdelicGroup) • originalDegreePoint 1)) := by
  congr 1
  funext q
  rw [← adelicDegreeShift_smul_one n, ← mul_smul,
    ← adelicDegreeShift_comm_torus n q.val q.ne_zero, mul_smul, hK₀]

/-- The same degree-independence holds for any renormalization functional defined on the positive
primitive torus cone `CoupledOrbit.Primitive`. -/
theorem local_invariant_primitive_diagonal_const
    (K₀ : GlobalSpace → GlobalSpace → ℝ)
    (hK₀ : ∀ (g : AdelicGroup) (x y : GlobalSpace), K₀ (g • x) (g • y) = K₀ x y)
    (ℛ : (CoupledOrbit.Primitive → ℝ) → ℝ) (n : ℕ+) :
    ℛ (fun p : CoupledOrbit.Primitive =>
        let q : ℚ := (p.val.1 : ℚ) / p.val.2
        have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast p.property.1.ne')
          (by exact_mod_cast (p.property.1.trans p.property.2.1).ne')
        K₀ (originalDegreePoint n) ((torusElem q hq : AdelicGroup) • originalDegreePoint n)) =
      ℛ (fun p : CoupledOrbit.Primitive =>
        let q : ℚ := (p.val.1 : ℚ) / p.val.2
        have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast p.property.1.ne')
          (by exact_mod_cast (p.property.1.trans p.property.2.1).ne')
        K₀ (originalDegreePoint 1) ((torusElem q hq : AdelicGroup) • originalDegreePoint 1)) := by
  congr 1
  funext p
  dsimp only
  rw [← adelicDegreeShift_smul_one n, ← mul_smul,
    ← adelicDegreeShift_comm_torus n _ _, mul_smul, hK₀]

/-! ## 2. Dyadic `-¼ N log N` divergence against the scale-invariant scattering tower -/

/-- Mass-normalized dyadic degree-block pairing on `[N, 2N)` with weights `√n / N`. -/
def dyadicNormalizedPairing (B : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) ^ 2)⁻¹ *
    ∑ m ∈ Ico N (2 * N), ∑ n ∈ Ico N (2 * N), Real.sqrt m * Real.sqrt n * B m n

/-- **Explicit dyadic upper bound.** Any pairing `B` agreeing with `weilDeltaKernel` off the
diagonal whose diagonal satisfies `B n n ≤ C * (1 + log n)` obeys
`dyadicNormalizedPairing B N ≤ 2 |C| (1 + log(2N)) + (17/4) N - (1/4) N log N` for all `N ≥ 1`. -/
theorem dyadicNormalizedPairing_le_of_log_diag {B : ℕ → ℕ → ℝ} {C : ℝ}
    (hoff : ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → B m n = weilDeltaKernel m n)
    (hdiag : ∀ n : ℕ, 0 < n → B n n ≤ C * (1 + Real.log n))
    {N : ℕ} (hN : 1 ≤ N) :
    dyadicNormalizedPairing B N ≤
      2 * |C| * (1 + Real.log (2 * (N : ℝ))) + (17 / 4) * (N : ℝ) -
        (1 / 4) * (N : ℝ) * Real.log N := by
  let S := Ico N (2 * N)
  have hS_pos : ∀ n ∈ S, 0 < n := fun n hn => lt_of_lt_of_le Nat.zero_lt_one
    (hN.trans (Finset.mem_Ico.mp hn).1)
  have hcard : (S.card : ℝ) = N := by
    dsimp only [S]
    rw [Nat.card_Ico, show 2 * N - N = N by omega]
  have hsplit : ∑ m ∈ S, ∑ n ∈ S, Real.sqrt m * Real.sqrt n * B m n =
      ∑ n ∈ S, (n : ℝ) * B n n +
        ∑ m ∈ S, ∑ n ∈ S, if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n) := by
    have hterm : ∀ m ∈ S, ∀ n ∈ S, Real.sqrt m * Real.sqrt n * B m n =
        (if m = n then (n : ℝ) * B n n else 0) +
          (if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n)) := by
      intro m hm n hn
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, if_pos rfl, add_zero, Real.mul_self_sqrt (Nat.cast_nonneg m)]
      · rw [if_neg hmn, if_neg hmn, zero_add, hoff m n (hS_pos m hm) (hS_pos n hn) hmn,
          ← Real.sqrt_mul (Nat.cast_nonneg m)]
        unfold frobeniusIntersection
        ring
    calc ∑ m ∈ S, ∑ n ∈ S, Real.sqrt m * Real.sqrt n * B m n
        = ∑ m ∈ S, ∑ n ∈ S, ((if m = n then (n : ℝ) * B n n else 0) +
            (if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n))) :=
          Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => hterm m hm n hn
      _ = (∑ m ∈ S, ∑ n ∈ S, if m = n then (n : ℝ) * B n n else 0) +
            ∑ m ∈ S, ∑ n ∈ S, if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n) := by
          simp_rw [Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          simp [hm]
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, if m = n then (0 : ℝ) else (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
        4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
    intro m hm
    have hpt : ∀ n ∈ S,
        (if m = n then (0 : ℝ) else (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
          4 * N - (if m < n then (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) else 0) := by
      intro n hn
      have hm' := Finset.mem_Ico.mp hm
      have hn' := Finset.mem_Ico.mp hn
      have hsum_le : (m : ℝ) + n ≤ 4 * N := by exact_mod_cast (by omega : m + n ≤ 4 * N)
      by_cases hmn : m = n
      · subst hmn; simp
      rw [if_neg hmn]
      obtain ⟨hlo, -⟩ := frobeniusIntersection_block_bounds hm hn hmn
      by_cases hlt : m < n
      · rw [if_pos hlt]
        have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
        rw [abs_of_neg (by linarith), neg_sub] at hlo
        have hdiv : (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) =
            (N : ℝ) ^ 2 / (4 * ((n : ℝ) - m)) := by field_simp
        linarith
      · rw [if_neg hlt]
        have h0 : 0 ≤ (N : ℝ) ^ 2 / (4 * |(m : ℝ) - n|) := by positivity
        linarith
    calc _ ≤ ∑ n ∈ S, (4 * (N : ℝ) -
          (if m < n then (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) else 0)) :=
          Finset.sum_le_sum hpt
      _ = 4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
            ← Finset.sum_filter, Finset.mul_sum]
          have hf : S.filter (fun n => m < n) = Ico (m + 1) (2 * N) := by
            have hm' := Finset.mem_Ico.mp hm
            ext n; simp only [S, Finset.mem_filter, Finset.mem_Ico]; omega
          rw [hf]; ring
  have hoff_ub :
      (∑ m ∈ S, ∑ n ∈ S, if m = n then (0 : ℝ) else (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
        4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N) := by
    calc _ ≤ ∑ m ∈ S, (4 * N * N -
          (N : ℝ) ^ 2 / 4 * ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m)) :=
          Finset.sum_le_sum hrow
      _ = 4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 *
            ∑ m ∈ S, ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]
          ring
      _ ≤ 4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N) := by
          have hb := sum_block_ge N
          have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 4 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hb h4]
  have hdiag_ub : (∑ n ∈ S, (n : ℝ) * B n n) ≤
      2 * |C| * (N : ℝ) ^ 2 * (1 + Real.log (2 * (N : ℝ))) := by
    have hpt : ∀ n ∈ S, (n : ℝ) * B n n ≤
        2 * |C| * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by
      intro n hn
      have hn_mem := Finset.mem_Ico.mp hn
      have hn_pos : 0 < n := hS_pos n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hN.trans hn_mem.1)
      have hn2N : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn_mem.2.le
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      have hlog_le : Real.log (n : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by positivity) hn2N
      have hB_le : B n n ≤ |C| * (1 + Real.log (2 * (N : ℝ))) := by
        calc B n n ≤ C * (1 + Real.log n) := hdiag n hn_pos
          _ ≤ |C| * (1 + Real.log n) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          _ ≤ |C| * (1 + Real.log (2 * (N : ℝ))) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
      calc (n : ℝ) * B n n
          ≤ (n : ℝ) * (|C| * (1 + Real.log (2 * (N : ℝ)))) :=
            mul_le_mul_of_nonneg_left hB_le (Nat.cast_nonneg n)
        _ ≤ (2 * (N : ℝ)) * (|C| * (1 + Real.log (2 * (N : ℝ)))) :=
            mul_le_mul_of_nonneg_right hn2N (mul_nonneg (abs_nonneg C) (by linarith))
        _ = 2 * |C| * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by ring
    calc (∑ n ∈ S, (n : ℝ) * B n n)
        ≤ ∑ _n ∈ S, 2 * |C| * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) := Finset.sum_le_sum hpt
      _ = 2 * |C| * (N : ℝ) ^ 2 * (1 + Real.log (2 * (N : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
          ring
  unfold dyadicNormalizedPairing
  change ((N : ℝ) ^ 2)⁻¹ * ∑ m ∈ S, ∑ n ∈ S, Real.sqrt m * Real.sqrt n * B m n ≤ _
  rw [hsplit]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := sq_pos_of_pos hN0
  calc ((N : ℝ) ^ 2)⁻¹ * ((∑ n ∈ S, (n : ℝ) * B n n) +
        ∑ m ∈ S, ∑ n ∈ S, if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n))
      ≤ ((N : ℝ) ^ 2)⁻¹ * (2 * |C| * (N : ℝ) ^ 2 * (1 + Real.log (2 * (N : ℝ))) +
          (4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N))) :=
        mul_le_mul_of_nonneg_left (add_le_add hdiag_ub hoff_ub) (inv_nonneg.mpr hN2.le)
    _ = 2 * |C| * (1 + Real.log (2 * (N : ℝ))) + (17 / 4) * (N : ℝ) -
          (1 / 4) * (N : ℝ) * Real.log N := by
        field_simp [hN0.ne']
        ring

/-- **Divergence to `-∞` across dyadic scales.** Every pairing `B` matching `weilDeltaKernel`
off the diagonal with `B n n ≤ C * (1 + log n)` diverges to `-∞` on normalized dyadic degree
blocks. -/
theorem tendsto_atBot_dyadicNormalizedPairing {B : ℕ → ℕ → ℝ} {C : ℝ}
    (hoff : ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → B m n = weilDeltaKernel m n)
    (hdiag : ∀ n : ℕ, 0 < n → B n n ≤ C * (1 + Real.log n)) :
    Tendsto (dyadicNormalizedPairing B) atTop atBot := by
  refine tendsto_atBot.mpr fun M => ?_
  have hlog : ∀ᶠ N : ℕ in atTop, 40 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 40
  have hnat : ∀ᶠ N : ℕ in atTop, 2 + 48 * |C| + 2 * |M| ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 + 48 * |C| + 2 * |M|)
  filter_upwards [eventually_ge_atTop 2, hlog, hnat] with N hN2 hLN hNN
  have h1 : 1 ≤ N := by omega
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast h1
  have hub := dyadicNormalizedPairing_le_of_log_diag hoff hdiag h1
  have hlog2 : 1 + Real.log (2 * (N : ℝ)) ≤ 3 * Real.log (N : ℝ) := by
    rw [Real.log_mul two_ne_zero hN_pos.ne']
    have hl2 : Real.log 2 ≤ Real.log (N : ℝ) :=
      Real.log_le_log zero_lt_two (by exact_mod_cast hN2)
    linarith
  have hC_term : 2 * |C| * (1 + Real.log (2 * (N : ℝ))) ≤
      (1 / 8) * (N : ℝ) * Real.log (N : ℝ) := by
    calc 2 * |C| * (1 + Real.log (2 * (N : ℝ)))
        ≤ 2 * |C| * (3 * Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = (6 * |C|) * Real.log (N : ℝ) := by ring
      _ ≤ ((1 / 8) * (N : ℝ)) * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M]) (by linarith)
      _ = (1 / 8) * (N : ℝ) * Real.log (N : ℝ) := by ring
  have hmain : (17 / 4) * (N : ℝ) - (1 / 8) * (N : ℝ) * Real.log (N : ℝ) ≤
      -(3 / 4) * (N : ℝ) := by
    have hfactor : (17 / 4) * (N : ℝ) - (1 / 8) * (N : ℝ) * Real.log (N : ℝ) =
        (N : ℝ) * (17 / 4 - Real.log (N : ℝ) / 8) := by ring
    rw [hfactor]
    calc (N : ℝ) * (17 / 4 - Real.log (N : ℝ) / 8)
        ≤ (N : ℝ) * (17 / 4 - 40 / 8) :=
          mul_le_mul_of_nonneg_left (by linarith) hN_pos.le
      _ = -(3 / 4) * (N : ℝ) := by ring
  have hM_le : -(3 / 4) * (N : ℝ) ≤ M := by
    have h1M : -|M| ≤ M := neg_abs_le M
    linarith [abs_nonneg C, abs_nonneg M]
  linarith

/-- **No torus-invariant local kernel glues Weil's off-diagonal to a scale-bounded diagonal.**
For any `AdelicGroup`-invariant kernel `K₀` and any torus-orbit functional `ℛ : (ℚˣ → ℝ) → ℝ`, if
a degree pairing `B : ℕ → ℕ → ℝ` agrees with `weilDeltaKernel` off the diagonal and takes the
renormalized torus-orbit values of `K₀` on the diagonal, then `dyadicNormalizedPairing B N → -∞`
while the Robin-normalized scattering tower on `F_N(u) = F₀(u - log N)` converges at every scale
`N` to the fixed constant `weilQuad F₀`. -/
theorem torus_invariant_local_glued_form_diverges_from_tower
    (K₀ : GlobalSpace → GlobalSpace → ℝ)
    (hK₀ : ∀ (g : AdelicGroup) (x y : GlobalSpace), K₀ (g • x) (g • y) = K₀ x y)
    (ℛ : (ℚˣ → ℝ) → ℝ)
    (B : ℕ → ℕ → ℝ)
    (hoff : ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → B m n = weilDeltaKernel m n)
    (hdiag : ∀ n : ℕ+, B n n = ℛ (fun q : ℚˣ => K₀ (originalDegreePoint n)
      ((torusElem q.val q.ne_zero : AdelicGroup) • originalDegreePoint n)))
    {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀) :
    (∀ n : ℕ+, B n n = B 1 1) ∧
      Tendsto (dyadicNormalizedPairing B) atTop atBot ∧
      ∀ N : ℕ, Tendsto
        (fun M : ℕ => (geometricWeilEnergy (fun u => (F₀ (u - Real.log N) : ℂ)) M).re)
        atTop (𝓝 (weilQuad F₀)) := by
  have hconst : ∀ n : ℕ+, B n n = B 1 1 := fun n =>
    (hdiag n).trans ((local_invariant_torus_diagonal_const K₀ hK₀ ℛ n).trans (hdiag 1).symm)
  have hlog : ∀ n : ℕ, 0 < n → B n n ≤ |B 1 1| * (1 + Real.log n) := by
    intro n hn
    have h1 : B n n = B 1 1 := hconst ⟨n, hn⟩
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    calc B n n = B 1 1 := h1
      _ ≤ |B 1 1| * 1 := by rw [mul_one]; exact le_abs_self _
      _ ≤ |B 1 1| * (1 + Real.log n) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  exact ⟨hconst, tendsto_atBot_dyadicNormalizedPairing hoff hlog,
    fun N => tendsto_geometricWeilEnergy_shift_re_weilQuad hF₀ hF₀c (Real.log N)⟩

/-! ## 3. Exact discriminant defect and prime-cube jump on smoothed/Gram-coupled packets -/

/-- Unit-weight indicator at a single degree `k`. -/
def unitAtom (k : ℕ) : ℕ → ℝ :=
  fun n => if n = k then 1 else 0

theorem atomicTest_unitAtom {N k : ℕ} (hk : k ∈ Icc 1 N) (g : ℝ → ℝ) :
    atomicTest N (unitAtom k) g = fun u => g (u - Real.log k) := by
  funext u
  unfold atomicTest unitAtom
  rw [Finset.sum_eq_single_of_mem k hk]
  · simp
  · intro n _ hnk
    simp [hnk]

theorem integral_atomicTest_unitAtom_sq {N k : ℕ} (hk : k ∈ Icc 1 N) (g : ℝ → ℝ) :
    (∫ u, atomicTest N (unitAtom k) g u ^ 2) = ∫ u, g u ^ 2 := by
  rw [atomicTest_unitAtom hk]
  exact MeasureTheory.integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log k)

/-- Exact prime-cube jump of `selfIntersection`: `selfIntersection (p³) - selfIntersection p = 2 log p`. -/
theorem selfIntersection_prime_cube_sub_prime {p : ℕ} (hp : p.Prime) :
    selfIntersection (p ^ 3) - selfIntersection p = 2 * Real.log p := by
  rw [selfIntersection_eq (pow_pos hp.pos 3), selfIntersection_eq hp.pos,
    tameDifferent_prime_pow hp (by omega : (3 : ℕ) ≠ 0)]
  have ht := tameDifferent_prime_pow hp (by omega : (1 : ℕ) ≠ 0)
  rw [pow_one] at ht
  rw [ht, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- **Exact discriminant defect between Gram-coupled packets and the scattering tower.**
At the canonical archimedean constant `c₀ = -4 * regularMean - (log(4π) + γ) = 2 * gammaHardyPhaseRate 0`,
for every separated `C_c²` packet `f = atomicTest N x g`, the `r → 1⁻` limit of
`gramLockedPacket` differs from the `M → ∞` limit of `geometricWeilEnergy` by
`-(∫ u, g u ^ 2) * ∑_{n=1}^N x_n² selfIntersection n`. -/
theorem gramLocked_sub_scatteringTower_eq_neg_discriminant
    {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N)
    (x : ℕ → ℝ) :
    let c₀ : ℝ := -4 * CoupledOrbit.regularMean -
      (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)
    let f : ℝ → ℝ := atomicTest N x g
    Tendsto (gramLockedPacket g hg.continuous hgc N x c₀) (𝓝[<] 1)
        (𝓝 (weilQuad f - (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n)) ∧
      Tendsto (fun M : ℕ => (geometricWeilEnergy (fun u => (f u : ℂ)) M).re) atTop
        (𝓝 (weilQuad f)) := by
  intro c₀ f
  have hc₀ : c₀ = 2 * _root_.RHTower.gammaHardyPhaseRate 0 :=
    two_mul_gammaHardyPhaseRate_zero_eq.symm
  constructor
  · have hlim := tendsto_smoothLockedPacket_weil_normalization hg hgc hsupp hw x
    rw [← hc₀] at hlim
    exact hlim.congr fun r =>
      (gramLockedPacket_of_separated hg hgc hsupp hw x c₀ r).symm
  · exact tendsto_geometricWeilEnergy_re_weilQuad (contDiff_atomicTest hg N x)
      (hasCompactSupport_atomicTest hsupp N x)

/-- The exact difference `(lim_{r → 1⁻} gramLockedPacket) - (lim_{M → ∞} geometricWeilEnergy)` on
a separated `C_c²` packet for an arbitrary scalar counterterm `c ∈ ℝ`. -/
def separatedPacketTowerDiscrepancy (c : ℝ) (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) : ℝ :=
  (c - 2 * _root_.RHTower.gammaHardyPhaseRate 0) * (∫ u, atomicTest N x g u ^ 2) -
    (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n

theorem tendsto_gramLocked_and_tower_with_discrepancy
    {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N)
    (x : ℕ → ℝ) (c : ℝ) :
    let f : ℝ → ℝ := atomicTest N x g
    Tendsto (gramLockedPacket g hg.continuous hgc N x c) (𝓝[<] 1)
        (𝓝 (weilQuad f + separatedPacketTowerDiscrepancy c N x g)) ∧
      Tendsto (fun M : ℕ => (geometricWeilEnergy (fun u => (f u : ℂ)) M).re) atTop
        (𝓝 (weilQuad f)) := by
  intro f
  constructor
  · have hlim := tendsto_smoothLockedPacket hg hgc hsupp hw x c
    have heq : weilQuad f + (c - 2 * _root_.RHTower.gammaHardyPhaseRate 0) * (∫ u, f u ^ 2) -
        (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n =
        weilQuad f + separatedPacketTowerDiscrepancy c N x g := by
      unfold separatedPacketTowerDiscrepancy
      dsimp only [f]
      ring
    rw [heq] at hlim
    exact hlim.congr fun r =>
      (gramLockedPacket_of_separated hg hgc hsupp hw x c r).symm
  · exact tendsto_geometricWeilEnergy_re_weilQuad (contDiff_atomicTest hg N x)
      (hasCompactSupport_atomicTest hsupp N x)

/-- **Universal prime-cube jump for every scalar counterterm `c ∈ ℝ`.**
For every `c ∈ ℝ`, every prime `p`, every `N ≥ p³`, and every nonzero profile `g` (`0 < ∫ g²`),
the discrepancy between the `r → 1⁻` Gram-coupled packet limit and the `M → ∞` scattering-tower
limit jumps by `-2 (∫ g²) log p < 0` between the unit-mass atoms at `p` and `p³`. In particular,
no scalar counterterm `c` can make the discrepancy vanish at both `p` and `p³`. -/
theorem gramLocked_sub_scatteringTower_prime_cube_jump
    (c : ℝ) {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : p ^ 3 ≤ N)
    {g : ℝ → ℝ} (hg_pos : 0 < ∫ u, g u ^ 2) :
    separatedPacketTowerDiscrepancy c N (unitAtom (p ^ 3)) g -
        separatedPacketTowerDiscrepancy c N (unitAtom p) g =
      -2 * (∫ u, g u ^ 2) * Real.log p ∧
    (separatedPacketTowerDiscrepancy c N (unitAtom p) g ≠ 0 ∨
      separatedPacketTowerDiscrepancy c N (unitAtom (p ^ 3)) g ≠ 0) := by
  have hp_mem : p ∈ Icc 1 N := by
    refine Finset.mem_Icc.mpr ⟨hp.pos, ?_⟩
    have hp_le : p ≤ p ^ 3 := Nat.le_self_pow (by omega) p
    exact hp_le.trans hN
  have hp3_mem : p ^ 3 ∈ Icc 1 N :=
    Finset.mem_Icc.mpr ⟨pow_pos hp.pos 3, hN⟩
  have hsum_single : ∀ {k : ℕ}, k ∈ Icc 1 N →
      (∑ n ∈ Icc 1 N, unitAtom k n ^ 2 * selfIntersection n) = selfIntersection k := by
    intro k hk
    unfold unitAtom
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp
    · intro n _ hnk
      simp [hnk]
  have hjump : separatedPacketTowerDiscrepancy c N (unitAtom (p ^ 3)) g -
      separatedPacketTowerDiscrepancy c N (unitAtom p) g =
      -2 * (∫ u, g u ^ 2) * Real.log p := by
    unfold separatedPacketTowerDiscrepancy
    rw [integral_atomicTest_unitAtom_sq hp3_mem, integral_atomicTest_unitAtom_sq hp_mem,
      hsum_single hp3_mem, hsum_single hp_mem]
    have hdiff := selfIntersection_prime_cube_sub_prime hp
    linear_combination -(∫ u, g u ^ 2) * hdiff
  refine ⟨hjump, ?_⟩
  by_contra hboth
  push Not at hboth
  rw [hboth.2, hboth.1, sub_zero] at hjump
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  nlinarith [hg_pos, hlog]

/-! ## 4. Master refutation of Question (G) -/

/-- **Complete unconditional refutation of Question (G).**
The three individual components exist, yet no normalization of the coupled orbit sum on
`X = Γ \ (ℍ³ × V)` invariant under `T(ℚ)` and determined by the local `ℍ³` Laplacian and `{A_p}_p`
glues Weil's off-diagonal (contacts of the arithmetic square + archimedean jets) to the
Robin-normalized scattering-tower packet diagonal without a degree-dependent discriminant
counterterm:

1. **Constant-diagonal obstruction + `-¼ N log N` dyadic divergence:** Every `AdelicGroup`-invariant
   kernel `K₀` and torus-orbit functional `ℛ : (ℚˣ → ℝ) → ℝ` yields a constant diagonal `B(n, n) = B(1, 1)`,
   forcing `dyadicNormalizedPairing B N → -∞` whenever the off-diagonal matches `weilDeltaKernel`,
   whereas the scattering tower is shift-invariant on `C_c²` packets.
2. **Off-diagonal local-product obstructions:** On `adelicCriticalProduct`, identity evaluation at
   `(1, n)` gives `n / (n² - 1)` (erasing `Λ(n)`), non-colliding torus sums diverge for all `(m, n)`
   (with non-decaying Pell terms `> 1 / (2 m)` when `¬ IsSquare(mn)`), and square-ratio pairs
   collide in `ℍ³` at `q = 1 / k` with positive finite factor `k⁻²`.
3. **Bounded-place-rank Hecke obstruction:** Every word `L` of `< #S` prime adjacency operators
   vanishes between `[x_1]` and `[x_{∏ S}]` (`#S ≥ 2`) where `weilDeltaKernel 1 (∏ S) > 0`, and
   `A_p 1_{[x_p]} ([x_1]) = 0` for every prime `p`.
4. **Discriminant counterterm necessity:** On separated smoothed/Gram-coupled packets, the
   discrepancy against the scattering tower equals `-(∫ g²) ∑ x_n² selfIntersection n` at the
   archimedean digamma normalization and jumps by `-2 (∫ g²) log p ≠ 0` between `p` and `p³` for
   every scalar `c ∈ ℝ`. -/
theorem refutation_of_glued_carrier_question_G :
    -- (1) Every AdelicGroup-invariant kernel and torus-orbit functional forces a constant diagonal
    -- and `-∞` dyadic drift against the scale-invariant scattering tower:
    (∀ (K₀ : GlobalSpace → GlobalSpace → ℝ),
      (∀ (g : AdelicGroup) (x y : GlobalSpace), K₀ (g • x) (g • y) = K₀ x y) →
      ∀ (ℛ : (ℚˣ → ℝ) → ℝ) (B : ℕ → ℕ → ℝ),
      (∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → B m n = weilDeltaKernel m n) →
      (∀ n : ℕ+, B n n = ℛ (fun q : ℚˣ => K₀ (originalDegreePoint n)
        ((torusElem q.val q.ne_zero : AdelicGroup) • originalDegreePoint n))) →
      (∀ n : ℕ+, B n n = B 1 1) ∧ Tendsto (dyadicNormalizedPairing B) atTop atBot) ∧
    -- (2) The global critical product erases prime contacts at q = 1 and diverges over T(ℚ) for all (m, n):
    (∀ n : ℕ+, 1 < (n : ℕ) →
      adelicCriticalProduct (originalDegreePoint 1) (originalDegreePoint n) =
        (n : ℝ) / ((n : ℝ) ^ 2 - 1)) ∧
    (∀ m n : ℕ+, ¬ Summable (fun q : NonCollidingTorus m n =>
      adelicCriticalProduct (originalDegreePoint m)
        ((torusElem q.1.val q.1.ne_zero : AdelicGroup) • originalDegreePoint n))) ∧
    -- (3) Bounded-length prime operator words vanish where Weil's off-diagonal is strictly positive:
    (∀ (L : List {p : ℕ // p.Prime}) (S : Finset {p : ℕ // p.Prime}),
      L.length < S.card → 2 ≤ S.card →
      let N : ℕ+ := ⟨∏ p ∈ S, p.1, Finset.prod_pos fun p _ => p.2.pos⟩
      primeWord L (fun c => if c = originalDegreeClass N then 1 else 0)
        (originalDegreeClass 1) = 0 ∧ 0 < weilDeltaKernel 1 N) ∧
    -- (4) No scalar normalization c ∈ ℝ eliminates the discriminant jump between p and p³:
    (∀ (c : ℝ) {p : ℕ}, p.Prime → ∀ {N : ℕ}, p ^ 3 ≤ N →
      ∀ {g : ℝ → ℝ}, 0 < (∫ u, g u ^ 2) →
      separatedPacketTowerDiscrepancy c N (unitAtom (p ^ 3)) g -
        separatedPacketTowerDiscrepancy c N (unitAtom p) g =
          -2 * (∫ u, g u ^ 2) * Real.log p ∧
      (separatedPacketTowerDiscrepancy c N (unitAtom p) g ≠ 0 ∨
        separatedPacketTowerDiscrepancy c N (unitAtom (p ^ 3)) g ≠ 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K₀ hK₀ ℛ B hoff hdiag
    have hconst : ∀ n : ℕ+, B n n = B 1 1 := fun n =>
      (hdiag n).trans ((local_invariant_torus_diagonal_const K₀ hK₀ ℛ n).trans (hdiag 1).symm)
    have hlog : ∀ n : ℕ, 0 < n → B n n ≤ |B 1 1| * (1 + Real.log n) := by
      intro n hn
      have h1 : B n n = B 1 1 := hconst ⟨n, hn⟩
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      calc B n n = B 1 1 := h1
        _ ≤ |B 1 1| * 1 := by rw [mul_one]; exact le_abs_self _
        _ ≤ |B 1 1| * (1 + Real.log n) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    exact ⟨hconst, tendsto_atBot_dyadicNormalizedPairing hoff hlog⟩
  · exact fun n hn => adelicCriticalProduct_one_degree_eq hn
  · exact not_summable_adelicCriticalProduct_torus_noncolliding
  · exact primeWord_eq_zero_and_weilDeltaKernel_pos
  · intro c p hp N hN g hg
    exact gramLocked_sub_scatteringTower_prime_cube_jump c hp hN hg

#print axioms local_invariant_torus_diagonal_const
#print axioms dyadicNormalizedPairing_le_of_log_diag
#print axioms tendsto_atBot_dyadicNormalizedPairing
#print axioms torus_invariant_local_glued_form_diverges_from_tower
#print axioms gramLocked_sub_scatteringTower_eq_neg_discriminant
#print axioms gramLocked_sub_scatteringTower_prime_cube_jump
#print axioms refutation_of_glued_carrier_question_G

end GaloisForLFunctions.HyperbolicArakelovTheory.GluedCarrierNoGo
