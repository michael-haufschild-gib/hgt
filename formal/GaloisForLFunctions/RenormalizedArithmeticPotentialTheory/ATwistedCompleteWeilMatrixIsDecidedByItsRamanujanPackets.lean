import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTwistedCompleteWeilFormHasAPeriodicLimit
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasFiniteRamanujanApproximation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap

/-!
# A twisted complete Weil matrix is decided by its Ramanujan packets

Fix a profile `φ`, an overlap `c > 0` and a real twist `λ` with summable defect
`Σ_k |d_λ(k)| < ∞`. The twisted complete Weil matrix `W_λ(c,N) = W(c,N) + G_λ(c,N)` is the
complete Weil matrix plus the lag-sum gap of the twist (`twistedCompleteWeilMatrix`); its form is
the twisted Weil form of the atomic test (`inner_twistedCompleteWeilMatrix`).

* **Packet energies** (`tendsto_twisted_packet`). On the normalized Ramanujan packet
  `Σ_{m∈T} β_m r_m`, the twisted form tends to
  `E_λ(T,β) = Σ_m β_m² E_m(c) + 2 Σ_k d_λ(k) k^{-1/2} M(y·y(k·))`, `y = Σ β_m e_m`.
* **The gap is bounded** (`abs_inner_twistGapMatrix_le`): `|⟪G_λ x, x⟫| ≤ 2 Σ|d_λ| (1 + 2c e^c) ‖x‖²`.
* **The complement is expensive** (`exists_finite_orthogonal_gap`): the prime-defect reserve and
  finite Ramanujan approximation give, for every `T`, a finite conductor set beyond whose span
  `W ≥ T`.
* **Dichotomy.** If `E_λ(T,β) ≥ μ Σβ²` for every packet with `μ > 0`, the twisted matrix is
  eventually positive definite (`eventually_twistedCompleteWeilMatrix_posDef`); if some packet has
  `E_λ(T,β) < 0`, the twisted form is eventually negative on its atomic test
  (`eventually_twisted_packet_neg`).

So at a fixed overlap the sign of a twisted complete form is the sign of an explicit quadratic
form on finitely supported Ramanujan coordinates. The proof of positivity is a two-by-two Schur
estimate: the packet span is almost invariant, its complement costs at least `T`, and the twist
couples them by at most its bound.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry CompletedShell
open _root_.RHTower (vonMangoldtAtom)

/-! ### Hermitian forms -/

section LinearAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A Hermitian matrix whose form is positive on nonzero vectors is positive definite. -/
theorem posDef_of_inner_pos {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (h : ∀ x : EuclideanSpace ℝ I, x ≠ 0 → 0 < ⟪toEuclideanLin A x, x⟫) : A.PosDef := by
  refine hA.posDef_iff_eigenvalues_pos.mpr fun i => ?_
  have hv : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hne : hA.eigenvectorBasis i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv
    exact zero_ne_one hv
  have happ : toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hpos := h _ hne
  rwa [happ, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hpos

/-- The polarization identity of a symmetric form. -/
theorem inner_add_self_eq {A : Matrix I I ℝ} (hA : A.IsHermitian) (u v : EuclideanSpace ℝ I) :
    ⟪toEuclideanLin A (u + v), u + v⟫ =
      ⟪toEuclideanLin A u, u⟫ + 2 * ⟪toEuclideanLin A u, v⟫ + ⟪toEuclideanLin A v, v⟫ := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hvu : ⟪toEuclideanLin A v, u⟫ = ⟪toEuclideanLin A u, v⟫ := by
    rw [hsym v u, real_inner_comm]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hvu]
  ring

/-- **Polarization.** A symmetric form bounded by `b‖x‖²` on the diagonal is bounded by
`b‖x‖‖y‖`. -/
theorem abs_inner_le_of_abs_quadratic_le {A : Matrix I I ℝ} (hA : A.IsHermitian) {b : ℝ}
    (hb : ∀ x : EuclideanSpace ℝ I, |⟪toEuclideanLin A x, x⟫| ≤ b * ‖x‖ ^ 2)
    (x y : EuclideanSpace ℝ I) : |⟪toEuclideanLin A x, y⟫| ≤ b * ‖x‖ * ‖y‖ := by
  have key : ∀ t : ℝ, 0 < t →
      2 * |⟪toEuclideanLin A x, y⟫| ≤ b * (t * ‖x‖ ^ 2 + ‖y‖ ^ 2 / t) := by
    intro t ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    set u := Real.sqrt t • x with hu
    set v := (Real.sqrt t)⁻¹ • y with hv
    have huv : ⟪toEuclideanLin A u, v⟫ = ⟪toEuclideanLin A x, y⟫ := by
      rw [hu, hv, map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp
    have hneg : ⟪toEuclideanLin A (u + -v), u + -v⟫ =
        ⟪toEuclideanLin A u, u⟫ - 2 * ⟪toEuclideanLin A u, v⟫ + ⟪toEuclideanLin A v, v⟫ := by
      rw [inner_add_self_eq hA, map_neg, inner_neg_left, inner_neg_right, inner_neg_right, neg_neg]
      ring
    have h4 : 4 * ⟪toEuclideanLin A u, v⟫ =
        ⟪toEuclideanLin A (u + v), u + v⟫ - ⟪toEuclideanLin A (u + -v), u + -v⟫ := by
      rw [inner_add_self_eq hA, hneg]
      ring
    have hnu : ‖u‖ ^ 2 = t * ‖x‖ ^ 2 := by
      rw [hu, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht.le]
    have hnv : ‖v‖ ^ 2 = ‖y‖ ^ 2 / t := by
      rw [hv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ht.le]
      ring
    have hpar : ‖u + v‖ ^ 2 + ‖u + -v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      rw [← sub_eq_add_neg, norm_add_sq_real, norm_sub_sq_real]
      ring
    have h1 := hb (u + v)
    have h2 := hb (u + -v)
    rw [← huv]
    have habs : |4 * ⟪toEuclideanLin A u, v⟫| ≤ b * ‖u + v‖ ^ 2 + b * ‖u + -v‖ ^ 2 := by
      rw [h4]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at habs
    have : b * ‖u + v‖ ^ 2 + b * ‖u + -v‖ ^ 2 = 2 * (b * (t * ‖x‖ ^ 2 + ‖y‖ ^ 2 / t)) := by
      rw [← mul_add, hpar, hnu, hnv]
      ring
    linarith
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := key (‖y‖ / ‖x‖) (div_pos hy0 hx0)
  have he : ‖y‖ / ‖x‖ * ‖x‖ ^ 2 + ‖y‖ ^ 2 / (‖y‖ / ‖x‖) = 2 * (‖x‖ * ‖y‖) := by
    field_simp
    ring
  rw [he] at h
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The two-by-two Schur estimate.** Let `v_i` be almost orthonormal quasimodes of `W` with
residual `≤ ε`, let `W ≥ T` on their orthogonal complement, and let `G` be bounded by `b`. If the
form of `W + G` is at least `μ Σ a_i²` on every combination `Σ a_i v_i` and `T` exceeds
`b + (1 + 2b)²/μ + 1`, then `W + G` is positive definite. -/
theorem posDef_add_of_packets {W G : Matrix I I ℝ} (hW : W.IsHermitian) (hG : G.IsHermitian)
    (v : ι → EuclideanSpace ℝ I) (E : ι → ℝ) {ε b T μ : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεs : (Fintype.card ι : ℝ) * ε ≤ 1)
    (hres : ∀ i, ‖toEuclideanLin W (v i) - E i • v i‖ ≤ ε)
    (hgram : ∀ i j, |⟪v i, v j⟫ - if i = j then 1 else 0| ≤ ε)
    (hgap : ∀ x : EuclideanSpace ℝ I, (∀ i, ⟪x, v i⟫ = 0) →
      T * ‖x‖ ^ 2 ≤ ⟪toEuclideanLin W x, x⟫)
    (hb0 : 0 ≤ b) (hb : ∀ x : EuclideanSpace ℝ I, |⟪toEuclideanLin G x, x⟫| ≤ b * ‖x‖ ^ 2)
    (hμ : 0 < μ)
    (hpacket : ∀ a : ι → ℝ, μ * ∑ i, a i ^ 2 ≤
      ⟪toEuclideanLin (W + G) (∑ i, a i • v i), ∑ i, a i • v i⟫)
    (hT : b + (1 + 2 * b) ^ 2 / μ + 1 ≤ T) :
    (W + G).PosDef := by
  have hWG := hW.add hG
  refine posDef_of_inner_pos hWG fun x hx => ?_
  -- split `x` into its projection on the packet span and an orthogonal remainder
  obtain ⟨a, z, hxuz, hzv⟩ : ∃ a : ι → ℝ, ∃ z : EuclideanSpace ℝ I,
      x = (∑ i, a i • v i) + z ∧ ∀ i, ⟪z, v i⟫ = 0 := by
    let K := Submodule.span ℝ (Set.range v)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (K.starProjection_apply_mem x)
    refine ⟨a, x - K.starProjection x, by rw [ha]; abel, fun i => ?_⟩
    exact K.starProjection_inner_eq_zero x (v i) (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨u, hu⟩ : ∃ u, u = ∑ i, a i • v i := ⟨_, rfl⟩
  rw [← hu] at hxuz
  obtain ⟨α, hα⟩ : ∃ α, α = ∑ i, a i ^ 2 := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; exact sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt α := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hss : s ^ 2 = α := by rw [hs]; exact Real.sq_sqrt hα0
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = ‖z‖ := ⟨_, rfl⟩
  have hξ0 : 0 ≤ ξ := by rw [hξ]; exact norm_nonneg _
  have hcard : (∑ i, |a i|) ^ 2 ≤ (Fintype.card ι : ℝ) * α := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => |a i|)
    simpa only [sq_abs, card_univ, hα] using h
  have hsumabs0 : 0 ≤ ∑ i, |a i| := sum_nonneg fun i _ => abs_nonneg _
  -- the coefficient mass controls the packet norm
  have hunorm : ‖u‖ ^ 2 ≤ 2 * α := by
    have hexp : ‖u‖ ^ 2 = ∑ i, ∑ j, a i * a j * ⟪v i, v j⟫ := by
      rw [← real_inner_self_eq_norm_sq, hu]
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    have hdiag : ∑ i, ∑ j, a i * a j * (if i = j then (1 : ℝ) else 0) = α := by
      rw [hα]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
        (fun h => absurd (mem_univ i) h), if_pos rfl]
      ring
    have herr : |∑ i, ∑ j, a i * a j * (⟪v i, v j⟫ - if i = j then 1 else 0)| ≤
        ε * (∑ i, |a i|) ^ 2 := by
      calc |∑ i, ∑ j, a i * a j * (⟪v i, v j⟫ - if i = j then 1 else 0)|
          ≤ ∑ i, ∑ j, |a i| * |a j| * ε := by
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hgram i j) (by positivity)
        _ = ε * (∑ i, |a i|) ^ 2 := by
            rw [sq, sum_mul_sum, mul_sum]
            exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    have hsplit : ∑ i, ∑ j, a i * a j * ⟪v i, v j⟫ =
        α + ∑ i, ∑ j, a i * a j * (⟪v i, v j⟫ - if i = j then 1 else 0) := by
      rw [← hdiag, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    have hεα : ε * (∑ i, |a i|) ^ 2 ≤ α := by
      calc ε * (∑ i, |a i|) ^ 2 ≤ ε * ((Fintype.card ι : ℝ) * α) :=
            mul_le_mul_of_nonneg_left hcard hε0
        _ = ((Fintype.card ι : ℝ) * ε) * α := by ring
        _ ≤ 1 * α := mul_le_mul_of_nonneg_right hεs hα0
        _ = α := one_mul α
    rw [hexp, hsplit]
    linarith [(abs_le.mp herr).2]
  have hu_le : ‖u‖ ≤ 2 * s := by
    have h2 : ‖u‖ ^ 2 ≤ (2 * s) ^ 2 := by rw [mul_pow, hss]; linarith
    nlinarith [norm_nonneg u]
  -- the quasimode cross term
  have hcrossW : |⟪toEuclideanLin W u, z⟫| ≤ s * ξ := by
    have hexp : ⟪toEuclideanLin W u, z⟫ =
        ∑ i, a i * ⟪toEuclideanLin W (v i) - E i • v i, z⟫ := by
      rw [hu]
      simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, inner_sub_left,
        real_inner_comm z, hzv, mul_zero, sub_zero]
    rw [hexp]
    have hεsum : ε * ∑ i, |a i| ≤ s := by
      have hsq : (ε * ∑ i, |a i|) ^ 2 ≤ s ^ 2 := by
        rw [mul_pow, hss]
        calc ε ^ 2 * (∑ i, |a i|) ^ 2 ≤ ε ^ 2 * ((Fintype.card ι : ℝ) * α) :=
              mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
          _ = ε * ((Fintype.card ι : ℝ) * ε) * α := by ring
          _ ≤ 1 * 1 * α := by
              refine mul_le_mul_of_nonneg_right ?_ hα0
              exact mul_le_mul hε1 hεs (by positivity) zero_le_one
          _ = α := by ring
      nlinarith [mul_nonneg hε0 hsumabs0]
    calc |∑ i, a i * ⟪toEuclideanLin W (v i) - E i • v i, z⟫| ≤ ∑ i, |a i| * (ε * ξ) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [hξ]
          exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hres i)
            (norm_nonneg _))
      _ = ε * (∑ i, |a i|) * ξ := by rw [← sum_mul]; ring
      _ ≤ s * ξ := mul_le_mul_of_nonneg_right hεsum hξ0
  have hcrossG : |⟪toEuclideanLin G u, z⟫| ≤ 2 * b * s * ξ := by
    have h := abs_inner_le_of_abs_quadratic_le hG hb u z
    rw [← hξ] at h
    calc |⟪toEuclideanLin G u, z⟫| ≤ b * ‖u‖ * ξ := h
      _ ≤ b * (2 * s) * ξ := by gcongr
      _ = 2 * b * s * ξ := by ring
  -- the three pieces of the form
  have hform : ⟪toEuclideanLin (W + G) x, x⟫ = ⟪toEuclideanLin (W + G) u, u⟫ +
      2 * ⟪toEuclideanLin (W + G) u, z⟫ + ⟪toEuclideanLin (W + G) z, z⟫ := by
    rw [hxuz, inner_add_self_eq hWG]
  have hpk : μ * α ≤ ⟪toEuclideanLin (W + G) u, u⟫ := by
    have := hpacket a
    rwa [← hα, ← hu] at this
  have hzz : (T - b) * ξ ^ 2 ≤ ⟪toEuclideanLin (W + G) z, z⟫ := by
    have h1 := hgap z hzv
    have h2 := (abs_le.mp (hb z)).1
    rw [map_add, LinearMap.add_apply, inner_add_left]
    rw [← hξ] at h1 h2
    linarith
  have huz : |⟪toEuclideanLin (W + G) u, z⟫| ≤ (1 + 2 * b) * s * ξ := by
    rw [map_add, LinearMap.add_apply, inner_add_left]
    calc |⟪toEuclideanLin W u, z⟫ + ⟪toEuclideanLin G u, z⟫|
        ≤ |⟪toEuclideanLin W u, z⟫| + |⟪toEuclideanLin G u, z⟫| := abs_add_le _ _
      _ ≤ s * ξ + 2 * b * s * ξ := add_le_add hcrossW hcrossG
      _ = (1 + 2 * b) * s * ξ := by ring
  obtain ⟨C, hC⟩ : ∃ C, C = 1 + 2 * b := ⟨_, rfl⟩
  rw [← hC] at huz hT
  have hDμ : C ^ 2 + μ ≤ μ * (T - b) := by
    have hD : C ^ 2 / μ + 1 ≤ T - b := by linarith
    have := mul_le_mul_of_nonneg_left hD hμ.le
    rwa [mul_add, mul_one, mul_div_cancel₀ _ hμ.ne'] at this
  -- positivity of the two-by-two form
  have hlow : μ * s ^ 2 - 2 * C * s * ξ + (T - b) * ξ ^ 2 ≤ ⟪toEuclideanLin (W + G) x, x⟫ := by
    rw [hform, hss]
    have := (abs_le.mp huz).1
    linarith
  have hne : 0 < s ∨ 0 < ξ := by
    by_contra hcon
    push_neg at hcon
    have hs' : s = 0 := le_antisymm hcon.1 hs0
    have hξ' : ξ = 0 := le_antisymm hcon.2 hξ0
    have hu0 : u = 0 := by
      have : ‖u‖ ≤ 0 := by rw [← mul_zero (2 : ℝ), ← hs']; exact hu_le
      exact norm_le_zero_iff.mp this
    have hz0 : z = 0 := norm_eq_zero.mp (by rw [← hξ, hξ'])
    exact hx (by rw [hxuz, hu0, hz0, add_zero])
  have hkey : μ * (μ * s ^ 2 - 2 * C * s * ξ + (T - b) * ξ ^ 2) =
      (μ * s - C * ξ) ^ 2 + (μ * (T - b) - C ^ 2) * ξ ^ 2 := by ring
  have hsq : 0 < (μ * s - C * ξ) ^ 2 + (μ * (T - b) - C ^ 2) * ξ ^ 2 := by
    have hc2 : μ ≤ μ * (T - b) - C ^ 2 := by linarith
    rcases hne with hs1 | hξ1
    · rcases eq_or_lt_of_le hξ0 with hξz | hξp
      · rw [← hξz]
        have : 0 < (μ * s) ^ 2 := by positivity
        simpa using this
      · have : 0 < (μ * (T - b) - C ^ 2) * ξ ^ 2 :=
          mul_pos (hμ.trans_le hc2) (pow_pos hξp 2)
        nlinarith [sq_nonneg (μ * s - C * ξ)]
    · have : 0 < (μ * (T - b) - C ^ 2) * ξ ^ 2 := mul_pos (hμ.trans_le hc2) (pow_pos hξ1 2)
      nlinarith [sq_nonneg (μ * s - C * ξ)]
  have hquad : 0 < μ * s ^ 2 - 2 * C * s * ξ + (T - b) * ξ ^ 2 := by
    rw [← hkey] at hsq
    exact pos_of_mul_pos_right hsq hμ.le
  linarith

end LinearAlgebra

/-! ### The twisted complete Weil matrix -/

section Twisted

/-- The lag-sum gap of a real twist on the atom pairs, in atom-mass normalization. -/
def twistGapMatrix (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun a b => (∑ k ∈ range (lagRange (Real.log N + c / N + 1)), twistDefect lam k *
    (bumpCorr (atomDilate φ (c / N)) (Real.log k - (Real.log (b : ℕ) - Real.log (a : ℕ))) +
      bumpCorr (atomDilate φ (c / N)) (Real.log k - (Real.log (a : ℕ) - Real.log (b : ℕ))))) /
    ∫ u, atomDilate φ (c / N) u ^ 2

theorem twistGapMatrix_isHermitian (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (twistGapMatrix lam φ c N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [twistGapMatrix, star_trivial]
  congr 1
  exact sum_congr rfl fun k _ => by ring

/-- The **twisted complete Weil matrix**: the complete Weil matrix with `Λ` replaced by `λ`. -/
def twistedCompleteWeilMatrix (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  completeWeilMatrix φ c N + twistGapMatrix lam φ c N

theorem twistedCompleteWeilMatrix_isHermitian (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (twistedCompleteWeilMatrix lam φ c N).IsHermitian :=
  (completeWeilMatrix_isHermitian φ c N).add (twistGapMatrix_isHermitian lam φ c N)

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ} {c : ℝ}

/-- The form of the gap matrix is the normalized twisted gap of the atomic test. -/
theorem inner_twistGapMatrix (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪toEuclideanLin (twistGapMatrix lam φ c N) x, x⟫ =
      (weilQuadTw lam (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) -
        weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N)))) /
          ∫ u, atomDilate φ (c / N) u ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc hN0
  obtain ⟨hgd, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw0
  set g := atomDilate φ (c / N) with hg
  set G0 := ∫ u, g u ^ 2 with hG0
  set y := primeHorizonExtension x with hy
  set K := lagRange (Real.log N + c / N + 1) with hK
  set B : ℕ → ℕ → ℝ := fun a b => ∑ k ∈ range K, twistDefect lam k *
    (bumpCorr g (Real.log k - (Real.log b - Real.log a)) +
      bumpCorr g (Real.log k - (Real.log a - Real.log b))) with hB
  have hq : ⟪toEuclideanLin (twistGapMatrix lam φ c N) x, x⟫ =
      qf (twistGapMatrix lam φ c N) (fun n => x n) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, qf, bil]
    rfl
  have hsum : qf (twistGapMatrix lam φ c N) (fun n => x n) =
      (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, y a * y b * B a b) / G0 := by
    rw [qf_eq_sum, sum_div]
    rw [← sum_coe_sort (Icc 1 N) (fun a => (∑ b ∈ Icc 1 N, y a * y b * B a b) / G0)]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_div, ← sum_coe_sort (Icc 1 N) (fun b => y a * y b * B a b / G0)]
    refine sum_congr rfl fun b _ => ?_
    simp only [twistGapMatrix, hy, primeHorizonExtension_coe, hB, ← hg, ← hG0, ← hK]
    ring
  have hswap : ∀ k : ℕ, ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, y a * y b *
      (bumpCorr g (Real.log k - (Real.log b - Real.log a)) +
        bumpCorr g (Real.log k - (Real.log a - Real.log b))) =
      pairing (atomicTest N y g) k := by
    intro k
    rw [pairing_atomicTest hgd.continuous hgc]
    simp only [mul_add, sum_add_distrib]
    rw [Finset.sum_comm (s := Icc 1 N) (t := Icc 1 N)
      (f := fun a b => y a * y b * bumpCorr g (Real.log k - (Real.log a - Real.log b)))]
    rw [two_mul]
    congr 1
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hexpand : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, y a * y b * B a b =
      ∑ k ∈ range K, twistDefect lam k * pairing (atomicTest N y g) k := by
    have hA : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, y a * y b * B a b =
        ∑ k ∈ range K, twistDefect lam k * ∑ b ∈ Icc 1 N, y a * y b *
          (bumpCorr g (Real.log k - (Real.log b - Real.log a)) +
            bumpCorr g (Real.log k - (Real.log a - Real.log b))) := by
      intro a _
      simp only [hB, mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun b _ => by ring
    rw [sum_congr rfl hA, Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_sum, hswap k]
  rw [hq, hsum, hexpand, weilQuadTw_eq _ (supportedIn_atomicTest hgsupp hw0.le N y),
    add_sub_cancel_left]
  rfl

/-- The form of the twisted complete Weil matrix is the twisted Weil form of the atomic test. -/
theorem inner_twistedCompleteWeilMatrix (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪toEuclideanLin (twistedCompleteWeilMatrix lam φ c N) x, x⟫ =
      weilQuadTw lam (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) /
        ∫ u, atomDilate φ (c / N) u ^ 2 := by
  rw [twistedCompleteWeilMatrix, map_add, LinearMap.add_apply, inner_add_left,
    inner_twistGapMatrix hφ hsupp hc hN, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN,
    ← add_div]
  congr 1
  ring

/-- **The gap is bounded.** `|⟪G_λ x, x⟫| ≤ 2 Σ|d_λ| (1 + 2c e^c) ‖x‖²`. -/
theorem abs_inner_twistGapMatrix_le (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪toEuclideanLin (twistGapMatrix lam φ c N) x, x⟫| ≤
      2 * (∑' k, |twistDefect lam k|) * (1 + 2 * c * Real.exp c) * ‖x‖ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc hN0
  obtain ⟨hgd, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw0
  have hG0 : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  set g := atomDilate φ (c / N) with hg
  set f := atomicTest N (primeHorizonExtension x) g with hf
  have hfc := (contDiff_atomicTest hgd N (primeHorizonExtension x)).continuous
  have hfs := hasCompactSupport_atomicTest hgsupp N (primeHorizonExtension x)
  have hmass := integral_atomicTest_sq_le_fixed_overlap hgd.continuous hgc hc hN hgsupp
    (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at hmass
  set D := ∑' k, |twistDefect lam k| with hD
  have hD0 : 0 ≤ D := tsum_nonneg fun k => abs_nonneg _
  rw [inner_twistGapMatrix hφ hsupp hc hN, weilQuadTw_eq _ (supportedIn_atomicTest hgsupp hw0.le N _),
    add_sub_cancel_left, abs_div, abs_of_pos hG0, div_le_iff₀ hG0]
  calc |∑ k ∈ range (lagRange (Real.log N + c / N + 1)),
        (vonMangoldtAtom k - twistCoeff lam k) * pairing f k|
      ≤ ∑ k ∈ range (lagRange (Real.log N + c / N + 1)), |twistDefect lam k| * (2 * ∫ t, f t ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_pairing_le hfc hfs k) (abs_nonneg _)
    _ = (∑ k ∈ range (lagRange (Real.log N + c / N + 1)), |twistDefect lam k|) *
          (2 * ∫ t, f t ^ 2) := by rw [sum_mul]
    _ ≤ D * (2 * ((∫ u, g u ^ 2) * (1 + 2 * c * Real.exp c) * ‖x‖ ^ 2)) := by
        refine mul_le_mul (hlam.sum_le_tsum _ fun k _ => abs_nonneg _) ?_ (by positivity) hD0
        exact mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = 2 * D * (1 + 2 * c * Real.exp c) * ‖x‖ ^ 2 * ∫ u, g u ^ 2 := by ring

/-- `⟪x, r_m⟫` read on the integer interval. -/
theorem inner_ramanujanHorizonVector_eq {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (m : ℕ) : ⟪x, ramanujanHorizonVector m N⟫ =
      ∑ n ∈ Icc 1 N, primeHorizonExtension x n * ramanujanPoleProfile m n := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, ramanujanPoleProfile m n * x n) = _
  rw [← sum_coe_sort (Icc 1 N)]
  exact sum_congr rfl fun n _ => by rw [primeHorizonExtension_coe, mul_comm]

/-- **The complement of a finite Ramanujan span is expensive.** A prime-defect reserve gives, for
every level `T`, finitely many conductors beyond whose span the complete form is at least `T`. -/
theorem exists_finite_orthogonal_gap {a₀ β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a₀ * ‖x‖ ^ 2 + β₀ * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (T : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧ ∀ᶠ N : ℕ in atTop,
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (∀ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ = 0) →
          T * ‖x‖ ^ 2 ≤ ⟪toEuclideanLin (completeWeilMatrix φ c N) x, x⟫ := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    ((T - a₀) / β₀) (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨S, hS, ?_⟩
  filter_upwards [hres, eventually_ge_atTop 2] with N hN hN2 x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  set r := ‖x‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hx0
  set xh := r⁻¹ • x with hxh
  have hxh1 : ‖xh‖ = 1 := by
    rw [hxh, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0.ne']
  have horth : ∀ m ∈ S, ⟪xh, ramanujanHorizonVector m N⟫ = 0 := by
    intro m hm
    have h := hx m hm
    rw [normalizedRamanujanHorizonVector, real_inner_smul_right] at h
    have hs : (Real.sqrt (Real.log N))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hlog).ne'
    have h' : ⟪x, ramanujanHorizonVector m N⟫ = 0 := (mul_eq_zero.mp h).resolve_left hs
    rw [hxh, real_inner_smul_left, h', mul_zero]
  have hdef : (T - a₀) / β₀ < poleDefect N (primeHorizonExtension xh) := by
    by_contra hle
    push_neg at hle
    obtain ⟨a, ha⟩ := happ N (primeHorizonExtension xh)
      (by rw [sum_primeHorizonExtension_sq, hxh1]; norm_num) hle
    set q : ℕ → ℝ := fun n => ∑ m ∈ S, a m * ramanujanPoleProfile m n with hq
    have hcross : ∑ n ∈ Icc 1 N, primeHorizonExtension xh n * q n = 0 := by
      simp only [hq, mul_sum]
      rw [Finset.sum_comm]
      refine sum_eq_zero fun m hm => ?_
      have h := horth m hm
      rw [inner_ramanujanHorizonVector_eq] at h
      calc ∑ n ∈ Icc 1 N, primeHorizonExtension xh n * (a m * ramanujanPoleProfile m n)
          = a m * ∑ n ∈ Icc 1 N, primeHorizonExtension xh n * ramanujanPoleProfile m n := by
            rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
        _ = 0 := by rw [h, mul_zero]
    have hexp : ∑ n ∈ Icc 1 N, (primeHorizonExtension xh n - q n) ^ 2 =
        ∑ n ∈ Icc 1 N, primeHorizonExtension xh n ^ 2 -
          2 * ∑ n ∈ Icc 1 N, primeHorizonExtension xh n * q n + ∑ n ∈ Icc 1 N, q n ^ 2 := by
      rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    have hq0 : 0 ≤ ∑ n ∈ Icc 1 N, q n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
    rw [hexp, sum_primeHorizonExtension_sq, hxh1, hcross] at ha
    linarith
  have hE := hN xh
  rw [hxh1] at hE
  have hWxh : T ≤ ⟪toEuclideanLin (completeWeilMatrix φ c N) xh, xh⟫ := by
    have h1 : β₀ * ((T - a₀) / β₀) < β₀ * poleDefect N (primeHorizonExtension xh) :=
      mul_lt_mul_of_pos_left hdef hβ₀
    rw [mul_div_cancel₀ _ hβ₀.ne'] at h1
    have h2 : completeWeilEnergy φ c N xh = ⟪toEuclideanLin (completeWeilMatrix φ c N) xh, xh⟫ :=
      rfl
    linarith
  have hxr : x = r • xh := by rw [hxh, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  rw [hxr, map_smul, real_inner_smul_left, real_inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hWxh (sq_nonneg r)]

/-! ### Ramanujan packets -/

/-- The profile `y = Σ_{m∈T} β_m e_m` of a Ramanujan packet. -/
def packetProfile (T : Finset ℕ) (β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ T, β m * normalizedRamanujanMode m n

/-- A common period of a packet: the product of its conductors. -/
def packetPeriod (T : Finset ℕ) : ℕ := ∏ m ∈ T, m

theorem packetPeriod_pos {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) : 0 < packetPeriod T :=
  Finset.prod_pos hT

theorem packetProfile_periodic {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    Function.Periodic (packetProfile T β) (packetPeriod T) := by
  intro n
  unfold packetProfile
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨q, hq⟩ : m ∣ packetPeriod T := Finset.dvd_prod_of_mem _ hm
  rw [hq]
  congr 1
  simpa only [Nat.cast_id, Nat.mul_comm] using
    ((normalizedRamanujanMode_periodic (hT m hm)).nat_mul q) n

/-- The **limiting twisted energy** of the Ramanujan packet `Σ_{m∈T} β_m e_m` at overlap `c`. -/
def packetEnergy (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) (T : Finset ℕ) (β : ℕ → ℝ) : ℝ :=
  ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m +
    twistLimitEnergy lam (packetProfile T β) (packetPeriod T)

theorem primeHorizonExtension_packet {T : Finset ℕ} {β : ℕ → ℝ} {N n : ℕ} (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N) n =
      packetCoeff (packetProfile T β) N n := by
  rw [primeHorizonExtension, dif_pos hn]
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
    (∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N) = _
  rw [map_sum, packetCoeff, packetProfile, sum_div, sum_div]
  refine sum_congr rfl fun m _ => ?_
  simp only [map_smul, normalizedRamanujanHorizonVector, ramanujanHorizonVector, smul_eq_mul,
    PiLp.projₗ_apply, PiLp.smul_apply, PiLp.toLp_apply, ramanujanPoleProfile]
  ring

theorem atomicTest_congr {N : ℕ} {x x' : ℕ → ℝ} (h : ∀ n ∈ Icc 1 N, x n = x' n) (g : ℝ → ℝ) :
    atomicTest N x g = atomicTest N x' g := by
  funext u
  unfold atomicTest
  exact sum_congr rfl fun n hn => by rw [h n hn]

/-- **Packet energies.** The twisted complete form of a normalized Ramanujan packet tends to its
limiting twisted energy. -/
theorem tendsto_twisted_packet (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c) (hlam : Summable fun k => |twistDefect lam k|)
    {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ⟪toEuclideanLin (twistedCompleteWeilMatrix lam φ c N)
          (∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N⟫) atTop
      (𝓝 (packetEnergy lam φ c T β)) := by
  have hW := tendsto_inner_sum_quasimodes T hT β fun m hm =>
    CriticalArithmeticCorrelationTheory.tendsto_completeWeilMatrix_ramanujan_quasimode_norm
      hφ hsupp hM hc (hT m hm)
  have hG := tendsto_twistedGap_packet hφ hsupp hM hc hlam (packetPeriod_pos hT)
    (packetProfile_periodic hT β)
  refine (hW.add hG).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [twistedCompleteWeilMatrix, map_add, LinearMap.add_apply, inner_add_left,
    inner_twistGapMatrix hφ hsupp hc hN,
    atomicTest_congr (fun n hn => primeHorizonExtension_packet (T := T) (β := β) hn)]

/-- **Negativity.** A packet of negative limiting twisted energy makes the twisted Weil form
negative on its atomic test for all large `N`. -/
theorem eventually_twisted_packet_neg (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m)
    {β : ℕ → ℝ} (hneg : packetEnergy lam φ c T β < 0) :
    ∀ᶠ N : ℕ in atTop, weilQuadTw lam
      (atomicTest N (packetCoeff (packetProfile T β) N) (atomDilate φ (c / N))) < 0 := by
  have h := tendsto_twisted_packet hφ hsupp hM hc hlam hT β
  filter_upwards [h.eventually (gt_mem_nhds hneg), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hG0 : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  rw [inner_twistedCompleteWeilMatrix hφ hsupp hc hN1,
    atomicTest_congr (fun n hn => primeHorizonExtension_packet (T := T) (β := β) hn)] at hN
  by_contra hge
  push_neg at hge
  have := div_nonneg hge hG0.le
  linarith

/-- The ℕ-indexed coefficients of a function on a finite conductor set. -/
def subtypeCoeff (S : Finset ℕ) (a : S → ℝ) (m : ℕ) : ℝ := if h : m ∈ S then a ⟨m, h⟩ else 0

theorem sum_subtype_smul_eq {E : Type*} [AddCommMonoid E] [Module ℝ E] (S : Finset ℕ)
    (a : S → ℝ) (v : ℕ → E) :
    ∑ i : S, a i • v i = ∑ m ∈ S, subtypeCoeff S a m • v m := by
  rw [← sum_coe_sort S (fun m => subtypeCoeff S a m • v m)]
  refine sum_congr rfl fun i _ => ?_
  simp only [subtypeCoeff, dif_pos i.property]

theorem sum_subtype_sq_eq (S : Finset ℕ) (a : S → ℝ) :
    ∑ i : S, a i ^ 2 = ∑ m ∈ S, subtypeCoeff S a m ^ 2 := by
  rw [← sum_coe_sort S (fun m => subtypeCoeff S a m ^ 2)]
  refine sum_congr rfl fun i _ => ?_
  simp only [subtypeCoeff, dif_pos i.property]

theorem sum_single_smul {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid E]
    [Module ℝ E] (v : ι → E) (i : ι) : ∑ k, (Pi.single i 1 : ι → ℝ) k • v k = v i := by
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
    (fun h => absurd (mem_univ i) h), Pi.single_eq_same, one_smul]

/-- **Positivity.** If every Ramanujan packet has limiting twisted energy at least `μ Σβ²`, `μ > 0`,
the twisted complete Weil matrix is eventually positive definite. -/
theorem eventually_twistedCompleteWeilMatrix_posDef (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    {a₀ β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a₀ * ‖x‖ ^ 2 + β₀ * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hlam : Summable fun k => |twistDefect lam k|) {μ : ℝ} (hμ : 0 < μ)
    (hbot : ∀ T : Finset ℕ, (∀ m ∈ T, 0 < m) → ∀ β : ℕ → ℝ,
      μ * ∑ m ∈ T, β m ^ 2 ≤ packetEnergy lam φ c T β) :
    ∀ᶠ N : ℕ in atTop, (twistedCompleteWeilMatrix lam φ c N).PosDef := by
  set b := 2 * (∑' k, |twistDefect lam k|) * (1 + 2 * c * Real.exp c) with hb
  have hb0 : 0 ≤ b := by
    have := tsum_nonneg fun k => abs_nonneg (twistDefect lam k)
    positivity
  set Tg := b + (1 + 2 * b) ^ 2 / (μ / 2) + 1 with hTg
  obtain ⟨S, hS, hgapS⟩ := exists_finite_orthogonal_gap hβ₀ hres Tg
  set s := (Fintype.card S : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  set ε := 1 / (s + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by linarith)]; linarith
  have hεs : s * ε ≤ 1 := by
    rw [hε, mul_one_div, div_le_one (by linarith)]; linarith
  set δ := μ / (2 * (s + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδs : s * δ ≤ μ / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the packet form at horizon `N` and its coefficient matrix
  set v : ℕ → S → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun N i =>
    normalizedRamanujanHorizonVector i N with hv
  set q : ℕ → (S → ℝ) → ℝ := fun N a =>
    ⟪toEuclideanLin (twistedCompleteWeilMatrix lam φ c N) (∑ i, a i • v N i),
      ∑ i, a i • v N i⟫ with hq
  set A : ℕ → S → S → ℝ := fun N i j =>
    ⟪toEuclideanLin (twistedCompleteWeilMatrix lam φ c N) (v N i), v N j⟫ with hA
  have hpk : ∀ a : S → ℝ, Tendsto (fun N => q N a) atTop
      (𝓝 (packetEnergy lam φ c S (subtypeCoeff S a))) := by
    intro a
    have h := tendsto_twisted_packet hφ hsupp hM hc hlam hS (subtypeCoeff S a)
    refine h.congr fun N => ?_
    simp only [hq, hv]
    rw [sum_subtype_smul_eq S a (fun m => normalizedRamanujanHorizonVector m N)]
  have hqexp : ∀ N a, q N a = ∑ i, ∑ j, a i * a j * A N i j := by
    intro N a
    simp only [hq, hA, map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  have hsymm : ∀ N i j, A N j i = A N i j := by
    intro N i j
    simp only [hA]
    rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (twistedCompleteWeilMatrix_isHermitian lam φ c N)) (v N j) (v N i), real_inner_comm]
  -- polarization: each coefficient converges
  set L : S → S → ℝ := fun i j =>
    (packetEnergy lam φ c S (subtypeCoeff S (Pi.single i 1 + Pi.single j 1)) -
      packetEnergy lam φ c S (subtypeCoeff S (Pi.single i 1)) -
      packetEnergy lam φ c S (subtypeCoeff S (Pi.single j 1))) / 2 with hL
  have hAlim : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (L i j)) := by
    intro i j
    have h1 := hpk (Pi.single i 1 + Pi.single j 1)
    have h2 := hpk (Pi.single i 1)
    have h3 := hpk (Pi.single j 1)
    refine (((h1.sub h2).sub h3).div_const 2).congr fun N => ?_
    have hsi := sum_single_smul (v N) i
    have hsj := sum_single_smul (v N) j
    have hsij : ∑ k, (Pi.single i (1 : ℝ) + Pi.single j 1) k • v N k = v N i + v N j := by
      simp only [Pi.add_apply, add_smul, sum_add_distrib, hsi, hsj]
    simp only [hq]
    rw [hsij, hsi, hsj, inner_add_self_eq (twistedCompleteWeilMatrix_isHermitian lam φ c N)]
    simp only [hA]
    ring
  have hLform : ∀ a : S → ℝ, ∑ i, ∑ j, a i * a j * L i j =
      packetEnergy lam φ c S (subtypeCoeff S a) := by
    intro a
    have hlim : Tendsto (fun N => q N a) atTop (𝓝 (∑ i, ∑ j, a i * a j * L i j)) := by
      have := tendsto_finsetSum (univ : Finset S) fun i _ =>
        tendsto_finsetSum (univ : Finset S) fun j _ => (hAlim i j).const_mul (a i * a j)
      exact this.congr fun N => (hqexp N a).symm
    exact tendsto_nhds_unique hlim (hpk a)
  -- all finitely many approximations hold eventually
  have hev_res : ∀ᶠ N : ℕ in atTop, ∀ i : S,
      ‖toEuclideanLin (completeWeilMatrix φ c N) (v N i) -
        completedConductorEnergy φ c i • v N i‖ ≤ ε := by
    refine Filter.eventually_all.mpr fun i => ?_
    have h := CriticalArithmeticCorrelationTheory.tendsto_completeWeilMatrix_ramanujan_quasimode_norm
      hφ hsupp hM hc (hS i i.property)
    exact (h.eventually (ge_mem_nhds hε0)).mono fun N hN => hN
  have hev_gram : ∀ᶠ N : ℕ in atTop, ∀ i j : S,
      |⟪v N i, v N j⟫ - if i = j then 1 else 0| ≤ ε := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have h := ((tendsto_normalizedRamanujanHorizonVector_gram (hS i i.property)
      (hS j j.property)).sub_const (if (i : ℕ) = j then 1 else 0)).abs
    have hz : Tendsto (fun N : ℕ => |⟪v N i, v N j⟫ - if i = j then 1 else 0|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero, Subtype.ext_iff] using h
    exact (hz.eventually (ge_mem_nhds hε0)).mono fun N hN => hN
  have hev_coef : ∀ᶠ N : ℕ in atTop, ∀ i j : S, |A N i j - L i j| ≤ δ := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have h := ((hAlim i j).sub_const (L i j)).abs
    rw [sub_self, abs_zero] at h
    exact (h.eventually (ge_mem_nhds hδ0)).mono fun N hN => hN
  filter_upwards [hev_res, hev_gram, hev_coef, hgapS, eventually_ge_atTop 1]
    with N hNres hNgram hNcoef hNgap hN1
  refine posDef_add_of_packets (completeWeilMatrix_isHermitian φ c N)
    (twistGapMatrix_isHermitian lam φ c N) (v N) (fun i => completedConductorEnergy φ c i)
    hε0.le hε1 (by rw [← hs]; exact hεs) hNres hNgram ?_ hb0
    (fun x => abs_inner_twistGapMatrix_le hφ hsupp hM hc hlam hN1 x) (half_pos hμ) ?_ le_rfl
  · intro x hx
    exact hNgap x fun m hm => hx ⟨m, hm⟩
  · intro a
    have hval := hqexp N a
    have hlow := hbot S hS (subtypeCoeff S a)
    rw [← sum_subtype_sq_eq, ← hLform a] at hlow
    have herr : |∑ i, ∑ j, a i * a j * A N i j - ∑ i, ∑ j, a i * a j * L i j| ≤
        δ * (∑ i, |a i|) ^ 2 := by
      rw [← sum_sub_distrib]
      calc |∑ i, (∑ j, a i * a j * A N i j - ∑ j, a i * a j * L i j)|
          ≤ ∑ i, ∑ j, |a i| * |a j| * δ := by
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
            rw [← sum_sub_distrib]
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
            rw [← mul_sub, abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hNcoef i j) (by positivity)
        _ = δ * (∑ i, |a i|) ^ 2 := by
            rw [sq, sum_mul_sum, mul_sum]
            exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    have hcard : (∑ i, |a i|) ^ 2 ≤ s * ∑ i, a i ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset S)) (f := fun i => |a i|)
      simpa only [sq_abs, card_univ, hs] using h
    have hα0 : 0 ≤ ∑ i, a i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    have hq' : q N a = ⟪toEuclideanLin (completeWeilMatrix φ c N + twistGapMatrix lam φ c N)
        (∑ i, a i • v N i), ∑ i, a i • v N i⟫ := rfl
    rw [← hq', hval]
    have h1 := (abs_le.mp herr).1
    have h2 : δ * (∑ i, |a i|) ^ 2 ≤ δ * (s * ∑ i, a i ^ 2) :=
      mul_le_mul_of_nonneg_left hcard hδ0.le
    have h3 : δ * (s * ∑ i, a i ^ 2) ≤ μ / 2 * ∑ i, a i ^ 2 := by
      rw [← mul_assoc, mul_comm δ s]
      exact mul_le_mul_of_nonneg_right hδs hα0
    linarith

end Twisted

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
