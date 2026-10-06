import GaloisForLFunctions.RHTower.KuznetsovEisensteinTransform
import GaloisForLFunctions.RHTower.DeckCuspEigenvalueNonneg

/-!
# The Kuznetsov identity with explicit spectral data

For the Poincaré series `U = U(·|s₁, μ, v)` and the conjugate series `P = P(·|h̄_{s₂,ν}, w)`
(`Re s₁, Re s₂ > 1`, `μ, ν > 0`, `ρ(T)v = e(μ)v`, `ρ(T)w = e(−ν)w`), write `a₁ = s̄₁`, `a₂ = s̄₂` and

`W(b, ν) = 2^{b−3/2} Γ(b−½) Γ(b−½+ν) Γ(b−½−ν) / Γ(2b−1)`

for the Mellin transform of the Whittaker function.  Then

`2 Σ_{(c,d) reduced} ⟨v, ρ(M)⁻¹w⟩ e((μd−νa)/c) (c²)^{−a₂} V(a₁, a₂; μ, ν, c²)
  = 4 (2πμ)^{½−a₁} (2πν)^{½−a₂} [Σ_j ρ_j(v) conj ρ_j(w) W(a₁, ν_j) W(a₂, ν_j)
      + (4π)⁻¹ ∫ Σ_i η_i(v, t) conj η_i(w, t) W(a₁, it) W(a₂, it) dt]`

(`kuznetsov_explicit`), with `ν_j² = ¼ − λ_j` the spectral parameters of the cuspidal eigenbasis,
`ρ_j` the Whittaker coefficients of its eigenfunctions (`cuspCoeff`), `(e_i)` an orthonormal basis of
the cusp vectors `V_∞` and `η_i(v, t)` the corresponding Fourier coefficient of the deck Eisenstein
series on the critical line (`eisCoeff`).

The continuous part comes from the identification of the Eisenstein transforms: both transforms take
values in `V_∞` almost everywhere, so Parseval in `V_∞` expresses `⟨T̄U(t), T̄P(t)⟩` through the
coordinates `2⟨T̄U(t), e_i⟩ = Φ^U_{e_i}(½+it)` and `2⟨T̄P(t), e_i⟩ = Φ^P_{e_i}(½+it)`
(`inner_eisTransformL2_poinc_conj`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry MaassWhittaker

noncomputable section

variable {N : ℕ}

/-! ## The cusp vectors and their orthonormal basis -/

/-- The cusp vectors `V_∞` as a subspace. -/
def cuspVecSub (N : ℕ) : Submodule ℂ (DeckSpace N) where
  carrier := {v | IsCuspVec v}
  add_mem' := isCuspVec_add
  zero_mem' := isCuspVec_zero
  smul_mem' := fun c _ hv => isCuspVec_smul c hv

/-- An orthonormal basis of `V_∞`. -/
def cuspBasis (N : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℂ (cuspVecSub N))) ℂ (cuspVecSub N) :=
  stdOrthonormalBasis ℂ (cuspVecSub N)

/-- The basis vectors as cusp vectors. -/
def cuspBasisVec (N : ℕ) (i : Fin (Module.finrank ℂ (cuspVecSub N))) : DeckSpace N :=
  (cuspBasis N i : cuspVecSub N)

theorem isCuspVec_cuspBasisVec (i : Fin (Module.finrank ℂ (cuspVecSub N))) :
    IsCuspVec (cuspBasisVec N i) :=
  (cuspBasis N i).2

/-- **Parseval in `V_∞`.** -/
theorem inner_eq_sum_cuspBasisVec {x y : DeckSpace N} (hx : IsCuspVec x) (hy : IsCuspVec y) :
    ⟪x, y⟫_ℂ = ∑ i, ⟪x, cuspBasisVec N i⟫_ℂ * ⟪cuspBasisVec N i, y⟫_ℂ := by
  have h := (cuspBasis N).sum_inner_mul_inner (⟨x, hx⟩ : cuspVecSub N) ⟨y, hy⟩
  simp only [Submodule.coe_inner] at h
  exact h.symm

/-! ## The continuous spectrum -/

/-- **The Eisenstein transforms of the two Poincaré series**:
`⟨T̄U, T̄P⟩ = ¼ ∫ Σ_i Φ^U_{e_i}(½+it) conj Φ^P_{e_i}(½+it) dt`. -/
theorem inner_eisTransformL2_poinc_conj (hN : 2 ≤ N) {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re)
    (hs₂ : 1 < s₂.re) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N}
    (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) :
    ⟪eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v)),
        eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w))⟫_ℂ =
      4⁻¹ * ∫ t : ℝ, ∑ i, poincEisPairing s₁ μ v (cuspBasisVec N i) n (1 / 2 + t * Complex.I) *
        conj (poincEisPairing (conj s₂) ν w (cuspBasisVec N i) m (1 / 2 + t * Complex.I)) := by
  set X := eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v))
  set Y := eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w))
  have hX := eisTransformL2_mem_symSpace hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v))
  have hY := eisTransformL2_mem_symSpace hN (toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w))
  have hXi := ae_all_iff.2 fun i =>
    eisTransformL2_poinc_inner hN hs₁ hμ hv hn (isCuspVec_cuspBasisVec (N := N) i)
  have hYi := ae_all_iff.2 fun i =>
    eisTransformL2_conj_inner hN hs₂ hν hw hm (isCuspVec_cuspBasisVec (N := N) i)
  rw [L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY, hXi, hYi] with t h1 h2 h3 h4
  rw [inner_eq_sum_cuspBasisVec h1.1 h2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h3 i, ← h4 i, map_mul, inner_conj_symm, map_ofNat]
  ring

/-! ## The Mellin transform of the Whittaker function -/

/-- `W(b, ν) = 2^{b−3/2} Γ(b−½) Γ(b−½+ν) Γ(b−½−ν) / Γ(2b−1)`. -/
def whittMellin (b ν : ℂ) : ℂ :=
  (2 : ℂ) ^ (b - 1 / 2 - 1) * Complex.Gamma (b - 1 / 2) * Complex.Gamma (b - 1 / 2 + ν) *
    Complex.Gamma (b - 1 / 2 - ν) / Complex.Gamma (2 * (b - 1 / 2))

theorem whittMellin_neg (b ν : ℂ) : whittMellin b (-ν) = whittMellin b ν := by
  unfold whittMellin
  rw [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem conj_ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (z : ℂ) : conj ((x : ℂ) ^ z) = (x : ℂ) ^ (conj z) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne),
    Complex.conj_ofReal]

theorem conj_whittMellin (b ν : ℂ) : conj (whittMellin b ν) = whittMellin (conj b) (conj ν) := by
  unfold whittMellin
  have h2 := conj_ofReal_cpow (x := 2) (by norm_num) (b - 1 / 2 - 1)
  push_cast at h2
  simp only [map_div₀, map_mul, ← Complex.Gamma_conj, map_sub, map_add, map_ofNat, map_one, h2]

/-- The pairing `Φ` in terms of `W`. -/
theorem poincEisPairing_eq (s₁ : ℂ) (μ : ℝ) (v w : DeckSpace N) (n : ℤ) (s : ℂ) :
    poincEisPairing s₁ μ v w n s = 2 * (eisCoeff s v w n *
      ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) * whittMellin (conj s₁) (s - 1 / 2)) :=
  rfl

/-! ## The spectral parameters -/

/-- The spectral parameter `ν` with `ν² = ¼ − λ`: `√(¼−λ)` for `λ ≤ ¼`, `i√(λ−¼)` otherwise. -/
def specParam (lam : ℝ) : ℂ :=
  if lam ≤ 1 / 4 then (Real.sqrt (1 / 4 - lam) : ℂ) else Complex.I * Real.sqrt (lam - 1 / 4)

theorem specParam_sq (lam : ℝ) : specParam lam ^ 2 = 1 / 4 - lam := by
  unfold specParam
  split_ifs with h
  · rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring
  · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring

theorem abs_re_specParam_le {lam : ℝ} (h : 0 ≤ lam) : |(specParam lam).re| ≤ 1 / 2 := by
  unfold specParam
  split_ifs with h'
  · rw [Complex.ofReal_re, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (1 / 4 - lam) ≤ Real.sqrt ((1 / 2) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  · simp

theorem conj_specParam (lam : ℝ) :
    conj (specParam lam) = specParam lam ∨ conj (specParam lam) = -specParam lam := by
  unfold specParam
  split_ifs
  · exact Or.inl (Complex.conj_ofReal _)
  · right
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

theorem conj_whittMellin_specParam (b : ℂ) (lam : ℝ) :
    conj (whittMellin b (specParam lam)) = whittMellin (conj b) (specParam lam) := by
  rw [conj_whittMellin]
  rcases conj_specParam lam with h | h
  · rw [h]
  · rw [h, whittMellin_neg]

/-! ## The cuspidal eigenfunctions and their Whittaker coefficients -/

/-- A cuspidal eigenfunction representing the `j`-th basis vector. -/
def cuspRep (j : CuspEigenIndex N) : ℍ → DeckSpace N := (cuspEigenBasis_spec j).choose

theorem isCuspLaplaceEigen_cuspRep (j : CuspEigenIndex N) :
    IsCuspLaplaceEigen N j.1 (cuspRep j) :=
  (cuspEigenBasis_spec j).choose_spec.choose

theorem cuspEigenBasis_eq_cuspRep (j : CuspEigenIndex N) :
    ((cuspEigenBasis N j : CuspidalL2 N) : DeckL2 N) =
      toDeckL2 (cuspRep j) (isCuspLaplaceEigen_cuspRep j).memLp :=
  (cuspEigenBasis_spec j).choose_spec.choose_spec

open Classical in
/-- The Whittaker coefficient `ρ_j(v)` of the `j`-th eigenfunction at a cusp vector of frequency `μ`:
its frequency-`μ` coefficient is `ρ_j(v) √y K_{ν_j}(2π|μ|y)`. -/
def cuspCoeff (j : CuspEigenIndex N) (μ : ℝ) (v : DeckSpace N) : ℂ :=
  if h : μ ≠ 0 ∧ IsCuspEigen μ v then
    (deckCuspCoeff_eigen_eq_whittaker (isCuspLaplaceEigen_cuspRep j) h.1 h.2
      (specParam_sq j.1)).choose
  else 0

theorem deckCuspCoeff_cuspRep (j : CuspEigenIndex N) {μ : ℝ} (hμ : μ ≠ 0) {v : DeckSpace N}
    (hv : IsCuspEigen μ v) {y : ℝ} (hy : 0 < y) :
    deckCuspCoeff μ v (cuspRep j) y =
      cuspCoeff j μ v * whittakerW (2 * Real.pi * |μ|) (specParam j.1) y := by
  rw [cuspCoeff, dif_pos ⟨hμ, hv⟩]
  exact (deckCuspCoeff_eigen_eq_whittaker (isCuspLaplaceEigen_cuspRep j) hμ hv
    (specParam_sq j.1)).choose_spec y hy

theorem abs_re_specParam_lt (j : CuspEigenIndex N) {s : ℂ} (hs : 1 < s.re) :
    |(specParam j.1).re| < s.re - 1 / 2 :=
  (abs_re_specParam_le (cuspEigenBasis_lam_nonneg j)).trans_lt (by linarith)

/-- **The Poincaré series against the `j`-th eigenfunction.** -/
theorem inner_poincL2_cuspEigenBasis {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ} (hμ : 0 < μ)
    {v : DeckSpace N} (hv : IsCuspEigen μ v) (j : CuspEigenIndex N) :
    ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v), (cuspEigenBasis N j : DeckL2 N)⟫_ℂ =
      2 * (cuspCoeff j μ v * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) *
        whittMellin (conj s₁) (specParam j.1)) := by
  rw [cuspEigenBasis_eq_cuspRep, inner_toDeckL2_toDeckL2]
  exact integral_inner_poincSeries_eigen hs₁ hμ hv (isCuspLaplaceEigen_cuspRep j)
    (abs_re_specParam_lt j hs₁) fun y hy => deckCuspCoeff_cuspRep j hμ.ne' hv hy

/-- **The `j`-th eigenfunction against the conjugate series.** -/
theorem inner_cuspEigenBasis_conjL2 {s₂ : ℂ} (hs₂ : 1 < s₂.re) {ν : ℝ} (hν : 0 < ν)
    {w : DeckSpace N} (hw : IsCuspEigen (-ν) w) (j : CuspEigenIndex N) :
    ⟪(cuspEigenBasis N j : DeckL2 N), toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w)⟫_ℂ =
      2 * (conj (cuspCoeff j (-ν) w) * ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(conj s₂ - 1 / 2)) *
        whittMellin (conj s₂) (specParam j.1)) := by
  rw [← inner_conj_symm, cuspEigenBasis_eq_cuspRep, inner_toDeckL2_toDeckL2,
    integral_inner_poincSeries_conjProfile_eigen hs₂ hν hw (isCuspLaplaceEigen_cuspRep j)
      (abs_re_specParam_lt j hs₂) fun y hy => deckCuspCoeff_cuspRep j (neg_ne_zero.mpr hν.ne') hw hy]
  have hk : (0 : ℝ) ≤ 2 * Real.pi * ν := by positivity
  rw [map_mul, map_mul, map_mul, map_ofNat, conj_ofReal_cpow hk, ← whittMellin, conj_whittMellin_specParam]
  simp only [map_neg, map_sub, map_div₀, map_one, map_ofNat]

/-! ## The explicit identity -/

/-- **The Kuznetsov identity with explicit spectral data** (parameters `a₁ = s̄₁`, `a₂ = s̄₂`). -/
theorem kuznetsov_explicit (hN : 2 ≤ N) {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re) (hs₂ : 1 < s₂.re)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen (-ν) w) {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) :
    2 * ∑' r : ReducedRow, rowWeight μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) *
        Kuznetsov.kuzValue (conj s₁) (conj s₂) μ ν ((r.1.1 0 : ℝ) ^ 2) =
      4 * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) *
        ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(conj s₂ - 1 / 2)) *
        ((∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
            whittMellin (conj s₁) (specParam j.1) * whittMellin (conj s₂) (specParam j.1)) +
          (4 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ, ∑ i, eisCoeff (1 / 2 + t * Complex.I) v (cuspBasisVec N i) n *
            conj (eisCoeff (1 / 2 + t * Complex.I) w (cuspBasisVec N i) m) *
            whittMellin (conj s₁) (t * Complex.I) * whittMellin (conj s₂) (t * Complex.I)) := by
  set K : ℂ := 4 * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) *
    ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(conj s₂ - 1 / 2))
  rw [kuznetsov_rough hN hs₁ hs₂ hμ hν hv hw, inner_eisTransformL2_poinc_conj hN hs₁ hs₂ hμ hν hv hw hn hm]
  have hd : ∀ j : CuspEigenIndex N,
      ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v), (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
        ⟪(cuspEigenBasis N j : DeckL2 N), toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w)⟫_ℂ =
      K * (cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
        whittMellin (conj s₁) (specParam j.1) * whittMellin (conj s₂) (specParam j.1)) := fun j => by
    rw [inner_poincL2_cuspEigenBasis hs₁ hμ hv j, inner_cuspEigenBasis_conjL2 hs₂ hν hw j]
    simp only [K]
    ring
  have hk : (0 : ℝ) ≤ 2 * Real.pi * ν := by positivity
  have hc : ∀ t : ℝ, ∑ i, poincEisPairing s₁ μ v (cuspBasisVec N i) n (1 / 2 + t * Complex.I) *
      conj (poincEisPairing (conj s₂) ν w (cuspBasisVec N i) m (1 / 2 + t * Complex.I)) =
      K * ∑ i, eisCoeff (1 / 2 + t * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + t * Complex.I) w (cuspBasisVec N i) m) *
        whittMellin (conj s₁) (t * Complex.I) * whittMellin (conj s₂) (t * Complex.I) := fun t => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hti : (1 / 2 + t * Complex.I) - 1 / 2 = t * Complex.I := by ring
    have hct : conj ((t : ℂ) * Complex.I) = -(t * Complex.I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [poincEisPairing_eq, poincEisPairing_eq, Complex.conj_conj, hti, map_mul, map_mul, map_mul,
      map_ofNat, conj_ofReal_cpow hk, conj_whittMellin, hct, whittMellin_neg]
    simp only [K, map_neg, map_sub, map_div₀, map_one, map_ofNat]
    ring
  simp_rw [hd, hc]
  rw [tsum_mul_left, integral_const_mul]
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
