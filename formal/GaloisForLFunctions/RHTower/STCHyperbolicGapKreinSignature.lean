import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia
import GaloisForLFunctions.RHTower.STCFlatGapSpectralBand

/-!
# Alternating signature of the flat Gamma gap correction

At a nonzero grade `g` the unique flat gap correction is `K_g(x,y) = S(g(x-y)/2)`, where
`S(t) = sinh t / t`.  It is the exponential kernel of the band measure `du/a` on `[-a/2,a/2]`,
`a = |g|`.  For strictly increasing nodes `x₁ < ⋯ < x_N` (for example prime logarithms) the packet
matrix `K_N = (K_g(x_i,x_j))` satisfies

* `(-1)^{N(N-1)/2} det K_N > 0`;
* `K_N` has exactly `⌈N/2⌉` positive and `⌊N/2⌋` negative directions, independent of the spacing
  and of the size of `g`;
* no invertible congruence makes `K_N` positive semidefinite once `N ≥ 2`;
* a correction of rank `r` leaves at least `⌊N/2⌋ - r` negative directions, so no correction of
  uniformly bounded rank makes every packet positive;
* the all-prime kernel is not the Hermitian form of any family of vectors in a space of finite
  negative index.
-/

open MeasureTheory Matrix Filter
open scoped ENNReal NNReal
open HTGeometry GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.NavierStokesRealExponentialVandermonde

namespace RHTower

noncomputable section

/-- The gap-sinc packet matrix `K_N = (S(g(x_i - x_j)/2))`. -/
def gapSincPacketMatrix (g : ℝ) {N : ℕ} (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => hyperbolicGapSinc (g * (x i - x j) / 2)

theorem gapSincPacketMatrix_isSymm (g : ℝ) {N : ℕ} (x : Fin N → ℝ) :
    (gapSincPacketMatrix g x).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [gapSincPacketMatrix, of_apply]
  rw [← hyperbolicGapSinc_even]
  congr 1
  ring

instance flatGapBandMeasure_isNegInvariant (a : ℝ) : (flatGapBandMeasure a).IsNegInvariant :=
  ⟨(measurePreserving_neg_flatGapBand a).map_eq⟩

theorem integral_flatGapBandMeasure_real {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    ∫ u, f u ∂(flatGapBandMeasure a) = a⁻¹ * ∫ u in (-(a / 2))..(a / 2), f u := by
  unfold flatGapBandMeasure
  rw [integral_smul_nnreal_measure, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc, NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr ha.le),
    smul_eq_mul]

/-- **(2)** `K_g(x,y) = (1/a)∫_{-a/2}^{a/2} e^{ux} e^{-uy} du`: the packet matrix is the exponential
kernel of the band measure. -/
theorem gapSincPacketMatrix_eq_expKernel {g : ℝ} (hg : g ≠ 0) {N : ℕ} (x : Fin N → ℝ) :
    gapSincPacketMatrix g x = expKernelMatrix (flatGapBandMeasure |g|) x := by
  ext i j
  simp only [gapSincPacketMatrix, expKernelMatrix, of_apply]
  rw [integral_flatGapBandMeasure_real (abs_pos.2 hg), band_integral_exp (abs_pos.2 hg)]
  rcases abs_cases g with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  rw [← hyperbolicGapSinc_even (g * (x i - x j) / 2)]
  congr 1
  ring

/-- The band `[-a/2, a/2]` supports any number of distinct points. -/
theorem flatGapBand_support {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∃ c : Fin N → ℝ, Function.Injective c ∧
      ∀ i, ∀ r > 0, 0 < flatGapBandMeasure a (Metric.ball (c i) r) := by
  have hD : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
  refine ⟨fun i => a * ((i : ℕ) : ℝ) / (2 * ((N : ℝ) + 1)), fun i j hij => ?_, fun i r hr => ?_⟩
  · simp only at hij
    rw [div_left_inj' hD.ne', mul_right_inj' ha.ne'] at hij
    exact Fin.ext (by exact_mod_cast hij)
  · set c := a * ((i : ℕ) : ℝ) / (2 * ((N : ℝ) + 1))
    have hc0 : 0 ≤ c := by positivity
    have hc1 : c < a / 2 := by
      have hi : ((i : ℕ) : ℝ) < (N : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_of_lt i.2
      rw [div_lt_div_iff₀ hD (by norm_num)]
      nlinarith
    have hsub : Set.Ioo c (min (c + r) (a / 2)) ⊆
        Metric.ball c r ∩ Set.Icc (-(a / 2)) (a / 2) := by
      intro u hu
      have h1 := min_le_left (c + r) (a / 2)
      have h2 := min_le_right (c + r) (a / 2)
      refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1, hu.2]
      · linarith [hu.1]
      · linarith [hu.2]
    unfold flatGapBandMeasure
    rw [Measure.smul_apply, Measure.restrict_apply Metric.isOpen_ball.measurableSet,
      ENNReal.smul_def, smul_eq_mul]
    refine ENNReal.mul_pos (by simp [ha]) (lt_of_lt_of_le ?_ (measure_mono hsub)).ne'
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 (lt_min (by linarith) hc1))

/-- **(1) Exact inertia on every packet.** For `g ≠ 0` and strictly increasing nodes,
`(-1)^{N(N-1)/2} det K_N > 0`, and `K_N` has `⌊N/2⌋` negative, `⌈N/2⌉` positive and no null
directions. -/
theorem gapSincPacket_inertia {g : ℝ} (hg : g ≠ 0) {N : ℕ} {x : Fin N → ℝ} (hx : StrictMono x) :
    0 < (-1 : ℝ) ^ (N * (N - 1) / 2) * (gapSincPacketMatrix g x).det ∧
      hermNegIndex ((gapSincPacketMatrix g x).map ((↑) : ℝ → ℂ)) = N / 2 ∧
      hermPosIndex ((gapSincPacketMatrix g x).map ((↑) : ℝ → ℂ)) = (N + 1) / 2 ∧
      hermNullIndex ((gapSincPacketMatrix g x).map ((↑) : ℝ → ℂ)) = 0 := by
  have ha := abs_pos.2 hg
  rw [gapSincPacketMatrix_eq_expKernel hg]
  exact ⟨expKernelMatrix_det_sign _ (flatGapBand_ae_bound _) (flatGapBand_support ha N) hx,
    expKernelMatrix_inertia _ (flatGapBand_ae_bound _) (flatGapBand_support ha N) hx⟩

theorem gapSincPacket_det_ne_zero {g : ℝ} (hg : g ≠ 0) {N : ℕ} {x : Fin N → ℝ}
    (hx : StrictMono x) : (gapSincPacketMatrix g x).det ≠ 0 := by
  intro h
  have := (gapSincPacket_inertia hg hx).1
  rw [h, mul_zero] at this
  exact lt_irrefl _ this

/-- The inertia as eigenvalue counts of the Hermitian packet matrix. -/
theorem gapSincPacket_eigenvalue_counts {g : ℝ} (hg : g ≠ 0) {N : ℕ} {x : Fin N → ℝ}
    (hx : StrictMono x) :
    ({i | (isHermitian_map_ofReal (gapSincPacketMatrix_isSymm g x)).eigenvalues i < 0} :
        Finset (Fin N)).card = N / 2 ∧
      ({i | 0 < (isHermitian_map_ofReal (gapSincPacketMatrix_isSymm g x)).eigenvalues i} :
        Finset (Fin N)).card = (N + 1) / 2 := by
  obtain ⟨-, hneg, hpos, -⟩ := gapSincPacket_inertia hg hx
  rw [negIndex_eq_card_neg_eigenvalues (isHermitian_map_ofReal (gapSincPacketMatrix_isSymm g x))]
    at hneg
  rw [posIndex_eq_card_pos_eigenvalues (isHermitian_map_ofReal (gapSincPacketMatrix_isSymm g x))]
    at hpos
  exact ⟨hneg, hpos⟩

open scoped ComplexOrder in
/-- **No congruence to a positive form.** For `N ≥ 2` no invertible congruence makes the packet
matrix positive semidefinite. -/
theorem gapSincPacket_not_congruent_posSemidef {g : ℝ} (hg : g ≠ 0) {N : ℕ} (hN : 2 ≤ N)
    {x : Fin N → ℝ} (hx : StrictMono x) {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsUnit S) :
    ¬ (Sᴴ * (gapSincPacketMatrix g x).map ((↑) : ℝ → ℂ) * S).PosSemidef := by
  rw [posSemidef_conjugate_iff _ hS,
    ← hermNegIndex_eq_zero_iff_posSemidef (isHermitian_map_ofReal (gapSincPacketMatrix_isSymm g x)),
    (gapSincPacket_inertia hg hx).2.1]
  omega

/-- **Prime packets.** For strictly increasing primes `p₁ < ⋯ < p_N` the packet on the prime
logarithms has `⌊N/2⌋` negative and `⌈N/2⌉` positive directions. -/
theorem gapSincPrimePacket_inertia {g : ℝ} (hg : g ≠ 0) {N : ℕ} {p : Fin N → ℕ}
    (hp : StrictMono p) (hprime : ∀ i, (p i).Prime) :
    hermNegIndex ((gapSincPacketMatrix g fun i => Real.log (p i)).map ((↑) : ℝ → ℂ)) = N / 2 ∧
      hermPosIndex ((gapSincPacketMatrix g fun i => Real.log (p i)).map ((↑) : ℝ → ℂ)) =
        (N + 1) / 2 := by
  have hx : StrictMono fun i => Real.log (p i) := fun i j hij =>
    Real.log_lt_log (by exact_mod_cast (hprime i).pos) (by exact_mod_cast hp hij)
  exact ⟨(gapSincPacket_inertia hg hx).2.1, (gapSincPacket_inertia hg hx).2.2.1⟩

/-- The all-prime gap kernel `(p, q) ↦ S(g(log p - log q)/2)`. -/
def gapSincPrimeKernel (g : ℝ) (p q : Nat.Primes) : ℂ :=
  (hyperbolicGapSinc (g * (Real.log p - Real.log q) / 2) : ℂ)

/-- The negative index of prime packets is unbounded. -/
theorem gapSincPrimeKernel_negIndex_unbounded {g : ℝ} (hg : g ≠ 0) (κ : ℕ) :
    ∃ (N : ℕ) (z : Fin N → Nat.Primes),
      κ < hermNegIndex (Matrix.of fun i j => gapSincPrimeKernel g (z i) (z j)) := by
  let z : Fin (2 * κ + 2) → Nat.Primes := fun i => ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩
  refine ⟨2 * κ + 2, z, ?_⟩
  have hmono : StrictMono fun i : Fin (2 * κ + 2) => Nat.nth Nat.Prime i :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).comp Fin.val_strictMono
  have h := (gapSincPrimePacket_inertia hg hmono fun i => Nat.prime_nth_prime i).1
  have e : (Matrix.of fun i j => gapSincPrimeKernel g (z i) (z j)) =
      (gapSincPacketMatrix g fun i => Real.log (Nat.nth Nat.Prime i)).map ((↑) : ℝ → ℂ) := rfl
  rw [e, h]
  omega

/-- **No finite-negative-index carrier.** The all-prime gap kernel is not the Hermitian form of
any family of vectors in a space whose negative-definite subspaces have dimension at most `κ`;
in particular no Pontryagin space of finite index carries all packet forms. -/
theorem gapSincPrimeKernel_no_pontryagin_carrier {g : ℝ} (hg : g ≠ 0) {V : Type*}
    [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (κ : ℕ)
    (hκ : ∀ W : Submodule ℂ V, (∀ v ∈ W, v ≠ 0 → (B v v).re < 0) →
      Module.finrank ℂ W ≤ κ) :
    ¬ ∃ φ : Nat.Primes → V, ∀ p q, B (φ p) (φ q) = gapSincPrimeKernel g p q :=
  no_finite_negIndex_carrier _ (gapSincPrimeKernel_negIndex_unbounded hg) B κ hκ

/-- **Rank cost of a repair.** Any correction `B` leaves at least `⌊N/2⌋ - rank B` negative
directions. -/
theorem gapSincPacket_negIndex_add_ge {g : ℝ} (hg : g ≠ 0) {N : ℕ} {x : Fin N → ℝ}
    (hx : StrictMono x) (B : Matrix (Fin N) (Fin N) ℂ) :
    N / 2 ≤ hermNegIndex ((gapSincPacketMatrix g x).map ((↑) : ℝ → ℂ) + B) + B.rank := by
  rw [← (gapSincPacket_inertia hg hx).2.1]
  exact hermNegIndex_le_add_rank _ B

/-- The same bound for a real correction, with its real rank. -/
theorem gapSincPacket_negIndex_add_real_ge {g : ℝ} (hg : g ≠ 0) {N : ℕ} {x : Fin N → ℝ}
    (hx : StrictMono x) (B : Matrix (Fin N) (Fin N) ℝ) :
    N / 2 ≤ hermNegIndex ((gapSincPacketMatrix g x + B).map ((↑) : ℝ → ℂ)) + B.rank := by
  have h := gapSincPacket_negIndex_add_ge hg hx (B.map ((↑) : ℝ → ℂ))
  rw [← Matrix.map_add _ (fun a b => Complex.ofReal_add a b)] at h
  have := rank_map_ofReal_le B
  omega

open scoped ComplexOrder in
/-- **No uniformly finite-channel repair.** Once `N ≥ 2r₀ + 2`, no real correction of rank at most
`r₀` makes the packet matrix positive semidefinite. -/
theorem gapSincPacket_no_finite_rank_repair {g : ℝ} (hg : g ≠ 0) {r₀ N : ℕ}
    (hN : 2 * r₀ + 2 ≤ N) {x : Fin N → ℝ} (hx : StrictMono x) {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : B.rank ≤ r₀) : ¬ ((gapSincPacketMatrix g x + B).map ((↑) : ℝ → ℂ)).PosSemidef := by
  intro hpsd
  have h0 := (hermNegIndex_eq_zero_iff_posSemidef hpsd.1).mpr hpsd
  have := gapSincPacket_negIndex_add_real_ge hg hx B
  omega

end

end RHTower
