import GaloisForLFunctions.HTGeometry.PositiveIntegerBlockOperators
import GaloisForLFunctions.HTGeometry.SchurKernelHalfLineCompression
import GaloisForLFunctions.RHTower.SoninCalkinNormBound
import GaloisForLFunctions.RHTower.WeylSpectrumCompactTransfer
import GaloisForLFunctions.RHTower.SoninOrthonormalCompactVanishing
import GaloisForLFunctions.RHTower.ThetaEulerPrimeResidueAverageVacuum

/-!
# Euler multiplication, the logarithmic cell clock and its residue channels

On `H = ℓ²(ℕ₊)` the literal Euler multiplication is `S_p e_n = e_{pn}`.  The logarithmic cells
`I_n = [log n, log(n+1))`, of length `ℓ_n = log((n+1)/n)`, give the cell isometry
`U e_n = 1_{I_n}/√ℓ_n` into `L²(0,∞)`; translating a cell by `log p` covers exactly the `p` cells
`I_{pn+r}`, so `U(H)` is invariant under the right translation `T_{log p}` and its pullback is
`W_p e_n = Σ_{r<p} c_{n,r} e_{pn+r}`, `c_{n,r} = √(ℓ_{pn+r}/ℓ_n)`, with `Σ_r c_{n,r}² = 1` and
`W_p W_q = W_{pq}`.  With the uniform channel `V_p e_n = p^{-1/2} Σ_r e_{pn+r}` and the residue
channel `R_p = S_p − p^{-1/2} V_p`:

* `W_p − V_p` is Hilbert–Schmidt, because `|c_{n,r} − p^{-1/2}| ≤ 1/(√p n)`;
* `‖S_p − W_p‖_ess = √(2 − 2/√p)` and `‖S_p W_p − W_p S_p‖_ess = √(2 − 2/p)`;
* `V_p* R_p = 0`, `R_p* R_p = (1 − 1/p) I`, and `S_p = p^{-1/2} W_p + R_p` modulo Hilbert–Schmidt;
* the residue channels of all primes are complete modulo the vacuum:
  `closure span{Ran R_p} = (ℂ e_1)^⊥`, `⋂_p ker R_p* = ℂ e_1` (prime-block maximum principle);
* every closed subspace containing the prime vectors and invariant under all `S_q` contains
  `ℓ²(ℕ_{≥2})`, while the closed span of the prime vectors alone is not invariant.

All operators are division-block operators `f ↦ w(m) f(⌊m/b⌋)`; the essential norms come from
the limits of their block masses.
-/

open Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry.PNatBlock

namespace RHTower

noncomputable section

local notation "ℓ²₊" => lp (fun _ : ℕ+ => ℂ) 2

/-! ## Essential norm of a division-block operator -/

/-- The unit vectors `e_{n+1}` of `ℓ²(ℕ₊)`. -/
def pnatUnit (n : ℕ) : ℓ²₊ := lp.single 2 (Nat.succPNat n) (1 : ℂ)

theorem orthonormal_pnatUnit : Orthonormal ℂ pnatUnit := by
  classical
  have h := (HilbertSchmidt.lpBasis ℕ+).orthonormal.comp _
    Nat.succPNat_injective
  convert h using 1
  funext n
  simp [pnatUnit, HilbertSchmidt.lpBasis_apply]

theorem norm_inner_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    ‖inner ℂ (((‖x‖ : ℂ))⁻¹ • x) x‖ = ‖x‖ := by
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal, norm_mul,
      norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    field_simp
    simp

theorem norm_normalize_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    ‖((‖x‖ : ℂ))⁻¹ • x‖ ≤ 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [inv_mul_cancel₀ h.ne']

/-- **Essential norm of a block operator.**  If the block masses tend to `β²`, then
`‖A_w‖_ess = β`: the tail blocks carry norm `β`, while finitely many blocks are compact. -/
theorem essentialNorm_divBlockOp {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    {β : ℝ} (hβ : 0 ≤ β) (hlim : Tendsto (fun q : ℕ => divBlockMass b w q) atTop (𝓝 (β ^ 2))) :
    essentialNorm (divBlockOp b w) = β := by
  classical
  haveI : NeZero b := ⟨hb.ne'⟩
  refine le_antisymm (essentialNorm_le_of_forall_exists _ β fun ε hε => ?_) ?_
  · have hlt : β ^ 2 < (β + ε) ^ 2 := by nlinarith
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hlt))
    set wN : ℕ → ℂ := fun m => if m / b ≤ N then w m else 0 with hwNdef
    have hwN : ∀ m, ‖wN m‖ ≤ K := fun m => by
      simp only [wN]; split_ifs
      · exact hw m
      · simpa using (norm_nonneg _).trans (hw 0)
    have hwd : ∀ m, ‖(w - wN) m‖ ≤ K + K := fun m =>
      (norm_sub_le _ _).trans (add_le_add (hw m) (hwN m))
    refine ⟨divBlockOp b wN, isCompactOperator_divBlockOp_of_le hb hwN (N := N)
      (fun m hm => by simp [wN, not_le.2 hm]), ?_⟩
    rw [← divBlockOp_sub hb hw hwN]
    refine (norm_divBlockOp_le hb hwd (sq_nonneg (β + ε)) fun q _ => ?_).trans
      (le_of_eq (Real.sqrt_sq (by linarith)))
    by_cases hqN : q ≤ N
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun r _ => ?_) (sq_nonneg _)
      simp [wN, div_block, hqN]
    · have heq : divBlockMass b (w - wN) q = divBlockMass b w q := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [wN, div_block, hqN]
      rw [heq]
      exact (hN q (by omega)).le
  · set A := divBlockOp b w
    have hnorm : ∀ n, ‖A (pnatUnit n)‖ = Real.sqrt (divBlockMass b w (n + 1)) := fun n => by
      have h := norm_sq_divBlockOp_single hb hw (Nat.succPNat n)
      rw [Nat.succPNat_coe] at h
      rw [← h, Real.sqrt_sq (norm_nonneg _)]
      rfl
    refine le_essentialNorm_of_pairing (T := A) (g := pnatUnit)
      (f := fun n => ((‖A (pnatUnit n)‖ : ℂ))⁻¹ • A (pnatUnit n)) (b := fun n => ‖A (pnatUnit n)‖)
      (fun n => norm_normalize_le _) (fun n => le_of_eq (orthonormal_pnatUnit.1 n))
      (tendsto_apply_orthonormal_atTop_zero orthonormal_pnatUnit)
      (Eventually.of_forall fun n => le_of_eq (norm_inner_normalize _).symm) ?_
    · simp_rw [hnorm]
      have := (hlim.comp (tendsto_add_atTop_nat 1)).sqrt
      rwa [Real.sqrt_sq hβ] at this

/-! ## Logarithmic cells -/

/-- The length `ℓ_n = log((n+1)/n)` of the logarithmic cell `[log n, log(n+1))`. -/
def logCell (n : ℕ) : ℝ := Real.log (n + 1) - Real.log n

theorem logCell_zero : logCell 0 = 0 := by simp [logCell]

theorem logCell_le {n : ℕ} (hn : 0 < n) : logCell n ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logCell, ← Real.log_div (by positivity) hn'.ne']
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
  field_simp
  ring

theorem le_logCell {n : ℕ} (hn : 0 < n) : 1 / (n + 1 : ℝ) ≤ logCell n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logCell, ← Real.log_div (by positivity) hn'.ne']
  refine le_trans (le_of_eq ?_) (Real.one_sub_inv_le_log_of_pos (by positivity))
  field_simp
  ring

theorem logCell_pos {n : ℕ} (hn : 0 < n) : 0 < logCell n :=
  lt_of_lt_of_le (by positivity) (le_logCell hn)

theorem logCell_nonneg (n : ℕ) : 0 ≤ logCell n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [logCell_zero]
  · exact (logCell_pos hn).le

/-- **Telescope.**  Translating a cell by `log p` covers exactly `p` cells:
`Σ_{r<p} ℓ_{np+r} = ℓ_n`. -/
theorem sum_logCell_block {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    ∑ r : Fin p, logCell (n * p + r) = logCell n := by
  rw [Fin.sum_univ_eq_sum_range (fun r => logCell (n * p + r)) p]
  have hstep : ∀ r, logCell (n * p + r) =
      Real.log ((n * p + (r + 1) : ℕ) : ℝ) - Real.log ((n * p + r : ℕ) : ℝ) := fun r => by
    simp only [logCell]
    push_cast
    ring_nf
  simp_rw [hstep]
  rw [Finset.sum_range_sub (fun r => Real.log ((n * p + r : ℕ) : ℝ)) p]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  push_cast
  rw [show (n : ℝ) * p + p = p * (n + 1) by ring, show (n : ℝ) * p + 0 = p * n by ring,
    Real.log_mul hp'.ne' (by positivity), Real.log_mul hp'.ne' hn'.ne', logCell]
  ring

/-- The cell weight `c(m) = √(ℓ_m / ℓ_{⌊m/p⌋})`. -/
def logCellWeight (p m : ℕ) : ℂ := (Real.sqrt (logCell m / logCell (m / p)) : ℝ)

theorem norm_logCellWeight (p m : ℕ) :
    ‖logCellWeight p m‖ = Real.sqrt (logCell m / logCell (m / p)) := by
  rw [logCellWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem logCell_div_le_one {p m : ℕ} (hp : 2 ≤ p) : logCell m / logCell (m / p) ≤ 1 := by
  rcases Nat.eq_zero_or_pos (m / p) with h0 | hk
  · rw [h0, logCell_zero, div_zero]; exact zero_le_one
  · have hm : 0 < m := lt_of_lt_of_le hk (Nat.div_le_self m p)
    have hkm : m / p + 1 ≤ m := by
      have := Nat.div_mul_le_self m p
      nlinarith
    rw [div_le_one (logCell_pos hk)]
    calc logCell m ≤ 1 / m := logCell_le hm
      _ ≤ 1 / ((m / p : ℕ) + 1 : ℝ) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast hkm
      _ ≤ logCell (m / p) := le_logCell hk

theorem norm_logCellWeight_le_one {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : ‖logCellWeight p m‖ ≤ 1 := by
  rw [norm_logCellWeight, Real.sqrt_le_one]
  exact logCell_div_le_one hp

/-- The cell weights of a block have unit square sum. -/
theorem divBlockMass_logCellWeight {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    divBlockMass p (logCellWeight p) q = 1 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hsq : ∀ r : Fin p, ‖logCellWeight p (q * p + r)‖ ^ 2 = logCell (q * p + r) / logCell q := by
    intro r
    rw [norm_logCellWeight, div_block, Real.sq_sqrt (div_nonneg (logCell_nonneg _) (logCell_nonneg _))]
  simp only [divBlockMass, hsq, ← Finset.sum_div, sum_logCell_block hp hq]
  exact div_self (logCell_pos hq).ne'

/-- **Cell weights are multiplicative**: `c_p(m) c_q(⌊m/p⌋) = c_{pq}(m)`. -/
theorem logCellWeight_mul (p q m : ℕ) :
    logCellWeight p m * logCellWeight q (m / p) = logCellWeight (p * q) m := by
  simp only [logCellWeight, ← Complex.ofReal_mul, Nat.div_div_eq_div_mul]
  congr 1
  rcases (logCell_nonneg (m / p)).eq_or_lt with h | h
  · rw [← h, div_zero, Real.sqrt_zero, zero_mul]
    have : logCell (m / (p * q)) = 0 := by
      rw [← Nat.div_div_eq_div_mul]
      rcases Nat.eq_zero_or_pos (m / p) with h0 | hk
      · rw [h0, Nat.zero_div, logCell_zero]
      · exact absurd h.symm (logCell_pos hk).ne'
    rw [this, div_zero, Real.sqrt_zero]
  · rw [← Real.sqrt_mul (div_nonneg (logCell_nonneg _) h.le)]
    congr 1
    field_simp

/-! ## The four multiplication operators -/

/-- The literal Euler multiplication `S_p e_n = e_{pn}`. -/
def eulerLabelShift (p : ℕ) : ℓ²₊ →L[ℂ] ℓ²₊ :=
  divBlockOp p (fun m => ((if p ∣ m then 1 else 0 : ℝ) : ℂ))

/-- The pulled-back logarithmic translation `W_p e_n = Σ_{r<p} c_{n,r} e_{pn+r}`. -/
def logCellShift (p : ℕ) : ℓ²₊ →L[ℂ] ℓ²₊ := divBlockOp p (logCellWeight p)

/-- The uniform residue channel `V_p e_n = p^{-1/2} Σ_{r<p} e_{pn+r}`. -/
def uniformResidueShift (p : ℕ) : ℓ²₊ →L[ℂ] ℓ²₊ :=
  divBlockOp p (fun _ => (((Real.sqrt p)⁻¹ : ℝ) : ℂ))

/-- The residue channel `R_p = S_p − p^{-1/2} V_p`. -/
def residueChannel (p : ℕ) : ℓ²₊ →L[ℂ] ℓ²₊ :=
  divBlockOp p (fun m => (((if p ∣ m then 1 else 0 : ℝ) - (p : ℝ)⁻¹ : ℝ) : ℂ))

theorem norm_labelWeight_le (p m : ℕ) : ‖(((if p ∣ m then 1 else 0 : ℝ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real]; split_ifs <;> simp

theorem norm_uniformWeight_le {p : ℕ} (hp : 0 < p) :
    ‖((((Real.sqrt p)⁻¹ : ℝ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast hp))

theorem norm_residueChannelWeight_le {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ‖((((if p ∣ m then 1 else 0 : ℝ) - (p : ℝ)⁻¹ : ℝ)) : ℂ)‖ ≤ 1 := by
  have h1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp)
  have h0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  split_ifs <;> constructor <;> linarith

theorem dvd_block_iff {p q : ℕ} (r : Fin p) : p ∣ q * p + r ↔ (r : ℕ) = 0 := by
  rw [Nat.dvd_add_right (dvd_mul_left p q)]
  exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h r.isLt, fun h => h ▸ dvd_zero p⟩

theorem sum_labelWeight_block {p : ℕ} (q : ℕ) (hp : 0 < p) (F : Fin p → ℝ) :
    ∑ r : Fin p, (if p ∣ q * p + r then 1 else 0 : ℝ) * F r = F ⟨0, hp⟩ := by
  rw [Finset.sum_eq_single ⟨0, hp⟩]
  · simp
  · intro r _ hr
    rw [if_neg, zero_mul]
    rw [dvd_block_iff]
    exact fun h => hr (Fin.ext h)
  · simp

/-- The indicator weight of `S_p`. -/
abbrev labelWeight (p : ℕ) (m : ℕ) : ℂ := ((if p ∣ m then 1 else 0 : ℝ) : ℂ)

/-- The uniform weight `p^{-1/2}` of `V_p`. -/
abbrev uniformWeight (p : ℕ) (_m : ℕ) : ℂ := (((Real.sqrt p)⁻¹ : ℝ) : ℂ)

/-- The residue weight `[p ∣ m] − 1/p` of `R_p`. -/
abbrev residueChannelWeight (p : ℕ) (m : ℕ) : ℂ := (((if p ∣ m then 1 else 0 : ℝ) - (p : ℝ)⁻¹ : ℝ) : ℂ)

theorem divBlockMass_sub_eq (b : ℕ) (w v : ℕ → ℂ) (q : ℕ) :
    divBlockMass b (w - v) q = divBlockMass b w q + divBlockMass b v q -
      2 * (divBlockGram b w v q).re := by
  simp only [divBlockMass, divBlockGram, Pi.sub_apply, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [@norm_sub_sq ℂ ℂ _ _ _ (w (q * b + r)) (v (q * b + r)), RCLike.inner_apply]
  simp [mul_comm]
  ring

theorem labelWeight_block {p q : ℕ} (r : Fin p) :
    labelWeight p (q * p + r) = if (r : ℕ) = 0 then 1 else 0 := by
  simp only [labelWeight, dvd_block_iff]
  split_ifs <;> simp

theorem divBlockMass_labelWeight {p : ℕ} (hp : 0 < p) (q : ℕ) : divBlockMass p (labelWeight p) q = 1 := by
  simp only [divBlockMass, labelWeight_block]
  rw [Finset.sum_eq_single ⟨0, hp⟩ (fun r _ hr => by simp [show (r : ℕ) ≠ 0 from fun h => hr (Fin.ext h)])
    (by simp)]
  simp

theorem divBlockMass_uniformWeight {p : ℕ} (hp : 0 < p) (q : ℕ) :
    divBlockMass p (uniformWeight p) q = 1 := by
  simp only [divBlockMass, uniformWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg p)]
  field_simp

theorem divBlockGram_uniform_residue {p : ℕ} (hp : 0 < p) (q : ℕ) :
    divBlockGram p (uniformWeight p) (residueChannelWeight p) q = 0 := by
  simp only [divBlockGram, uniformWeight, residueChannelWeight, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  rw [Complex.ofReal_eq_zero, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have h1 : ∑ r : Fin p, (if p ∣ q * p + r then 1 else 0 : ℝ) = 1 := by
    have := sum_labelWeight_block q hp (fun _ => 1)
    simpa using this
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  ring

theorem divBlockMass_residueChannelWeight {p : ℕ} (hp : 0 < p) (q : ℕ) :
    divBlockMass p (residueChannelWeight p) q = 1 - (p : ℝ)⁻¹ := by
  simp only [divBlockMass, residueChannelWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsq : ∀ r : Fin p, ((if p ∣ q * p + r then 1 else 0 : ℝ) - (p : ℝ)⁻¹) ^ 2 =
      (if p ∣ q * p + r then 1 else 0 : ℝ) * (1 - 2 * (p : ℝ)⁻¹) + ((p : ℝ)⁻¹) ^ 2 := fun r => by
    split_ifs <;> ring
  simp only [hsq, Finset.sum_add_distrib, sum_labelWeight_block q hp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  ring

theorem divBlockGram_residue_self {p : ℕ} (hp : 0 < p) (q : ℕ) :
    divBlockGram p (residueChannelWeight p) (residueChannelWeight p) q = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [divBlockGram_self, divBlockMass_residueChannelWeight hp]

/-! ### (1) Isometries and multiplicativity -/

theorem eulerLabelShift_eq (p : ℕ) : eulerLabelShift p = divBlockOp p (labelWeight p) := rfl

theorem norm_eulerLabelShift_apply {p : ℕ} (hp : 0 < p) (f : ℓ²₊) : ‖eulerLabelShift p f‖ = ‖f‖ :=
  norm_divBlockOp_apply_of_divBlockMass hp (norm_labelWeight_le p)
    (fun q _ => divBlockMass_labelWeight hp q) f

theorem norm_logCellShift_apply {p : ℕ} (hp : 2 ≤ p) (f : ℓ²₊) : ‖logCellShift p f‖ = ‖f‖ :=
  norm_divBlockOp_apply_of_divBlockMass (by omega) (norm_logCellWeight_le_one hp)
    (fun q hq => divBlockMass_logCellWeight (by omega) hq) f

theorem norm_uniformResidueShift_apply {p : ℕ} (hp : 0 < p) (f : ℓ²₊) :
    ‖uniformResidueShift p f‖ = ‖f‖ :=
  norm_divBlockOp_apply_of_divBlockMass hp (fun _ => norm_uniformWeight_le hp)
    (fun q _ => divBlockMass_uniformWeight hp q) f

/-- `S_p e_n = e_{pn}`. -/
theorem eulerLabelShift_single {p : ℕ} (hp : 0 < p) (n : ℕ+) :
    eulerLabelShift p (lp.single 2 n (1 : ℂ)) = lp.single 2 (⟨p, hp⟩ * n) (1 : ℂ) := by
  classical
  ext m
  have hiff : ((m : ℕ) / p = n ∧ p ∣ (m : ℕ)) ↔ m = ⟨p, hp⟩ * n := by
    constructor
    · rintro ⟨h1, h2⟩
      apply PNat.eq
      rw [PNat.mul_coe, PNat.mk_coe, ← h1, Nat.mul_div_cancel' h2]
    · rintro rfl
      rw [PNat.mul_coe, PNat.mk_coe]
      exact ⟨Nat.mul_div_cancel_left _ hp, dvd_mul_right _ _⟩
  rw [eulerLabelShift, divBlockOp_single_apply hp (norm_labelWeight_le p)]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h1 : (m : ℕ) / p = n <;> by_cases h2 : p ∣ (m : ℕ)
  · rw [if_pos h1, if_pos (hiff.1 ⟨h1, h2⟩)]; simp [h2]
  · rw [if_pos h1, if_neg (fun h => h2 (hiff.2 h).2)]; simp [h2]
  · rw [if_neg h1, if_neg (fun h => h1 (hiff.2 h).1)]
  · rw [if_neg h1, if_neg (fun h => h1 (hiff.2 h).1)]

/-- `W_p e_n = Σ_{r<p} c_{n,r} e_{pn+r}` with `c_{n,r} = √(ℓ_{pn+r}/ℓ_n)`. -/
theorem logCellShift_single_apply {p : ℕ} (hp : 2 ≤ p) (n m : ℕ+) :
    (logCellShift p (lp.single 2 n (1 : ℂ)) : ℕ+ → ℂ) m =
      if (m : ℕ) / p = n then ((Real.sqrt (logCell m / logCell n) : ℝ) : ℂ) else 0 := by
  rw [logCellShift, divBlockOp_single_apply (by omega) (norm_logCellWeight_le_one hp)]
  split_ifs with h
  · rw [logCellWeight, h]
  · rfl

theorem sum_sq_logCellWeight {p : ℕ} (hp : 0 < p) {n : ℕ} (hn : 0 < n) :
    ∑ r : Fin p, Real.sqrt (logCell (n * p + r) / logCell n) ^ 2 = 1 := by
  have hmass := divBlockMass_logCellWeight hp hn
  haveI : NeZero p := ⟨hp.ne'⟩
  simpa [divBlockMass, norm_logCellWeight, div_block] using hmass

/-- `W_p W_q = W_{pq}`. -/
theorem logCellShift_comp {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    logCellShift p ∘L logCellShift q = logCellShift (p * q) := by
  rw [logCellShift, logCellShift, divBlockOp_comp (by omega) (by omega) (norm_logCellWeight_le_one hp)
    (norm_logCellWeight_le_one hq), logCellShift]
  congr 1
  funext m
  exact logCellWeight_mul p q m

/-- `S_p S_q = S_{pq}`. -/
theorem eulerLabelShift_comp {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    eulerLabelShift p ∘L eulerLabelShift q = eulerLabelShift (p * q) := by
  rw [eulerLabelShift, eulerLabelShift, divBlockOp_comp hp hq (norm_labelWeight_le p)
    (norm_labelWeight_le q), eulerLabelShift]
  congr 1
  funext m
  rw [← Complex.ofReal_mul]
  congr 1
  by_cases h : p ∣ m
  · rw [if_pos h, one_mul]
    by_cases h2 : q ∣ m / p
    · rw [if_pos h2, if_pos ((Nat.dvd_div_iff_mul_dvd h).1 h2)]
    · rw [if_neg h2, if_neg (fun h' => h2 ((Nat.dvd_div_iff_mul_dvd h).2 h'))]
  · rw [if_neg h, zero_mul, if_neg (fun h' => h (dvd_trans (dvd_mul_right p q) h'))]

/-! ### (2) The continuum clock is the uniform residue channel modulo Hilbert–Schmidt -/

theorem abs_sqrt_sub_sqrt_le_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / Real.sqrt y := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [le_div_iff₀ hsy]
  calc |Real.sqrt x - Real.sqrt y| * Real.sqrt y
      ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) := by
        gcongr; linarith [Real.sqrt_nonneg x]
    _ = |x - y| := by
        rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x + Real.sqrt y), ← abs_mul,
          show (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) =
            Real.sqrt x ^ 2 - Real.sqrt y ^ 2 by ring, Real.sq_sqrt hx, Real.sq_sqrt hy.le]

/-- `|ℓ_{qp+r}/ℓ_q − 1/p| ≤ 1/(pq)`. -/
theorem abs_logCell_ratio_sub_le {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : r < p) :
    |logCell (q * p + r) / logCell q - 1 / p| ≤ 1 / (p * q) := by
  have hm : 0 < q * p + r := by positivity
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have ha1 := logCell_le hm
  have ha2 := le_logCell hm
  have hc1 := logCell_le hq
  have hc2 := le_logCell hq
  have hc0 := logCell_pos hq
  set a := logCell (q * p + r)
  set c := logCell q
  have hmle : ((q * p + r : ℕ) : ℝ) + 1 ≤ q * p + p := by
    have : (r : ℝ) + 1 ≤ p := by exact_mod_cast hr
    push_cast; linarith
  have hmge : (q : ℝ) * p ≤ ((q * p + r : ℕ) : ℝ) := by push_cast; linarith [(r.cast_nonneg : (0:ℝ) ≤ r)]
  -- `1/(q+1) ≤ p a ≤ 1/q`
  have hpa1 : p * a ≤ 1 / q := by
    calc p * a ≤ p * (1 / ((q * p + r : ℕ) : ℝ)) := by gcongr
      _ ≤ p * (1 / (q * p)) := by gcongr
      _ = 1 / q := by field_simp
  have hpa2 : 1 / (q + 1 : ℝ) ≤ p * a := by
    calc 1 / (q + 1 : ℝ) = p * (1 / (q * p + p)) := by field_simp
      _ ≤ p * (1 / (((q * p + r : ℕ) : ℝ) + 1)) := by gcongr
      _ ≤ p * a := by gcongr
  have hq1 : (0 : ℝ) < q + 1 := by linarith
  have h1 : c * q ≤ 1 := by rw [le_div_iff₀ hq'] at hc1; linarith
  have h2 : 1 ≤ p * a * (q + 1) := by rw [div_le_iff₀ hq1] at hpa2; linarith
  have h3 : 1 ≤ c * (q + 1) := by rw [div_le_iff₀ hq1] at hc2; linarith
  have h4 : p * a * q ≤ 1 := by rw [le_div_iff₀ hq'] at hpa1; linarith
  have hup : p * a - c ≤ c / q := by
    rw [le_div_iff₀ hq']; nlinarith
  have hlo : -(c / q) ≤ p * a - c := by
    rw [neg_le_sub_iff_le_add, ← sub_nonneg,
      show p * a + c / q - c = (p * a * q + c - c * q) / q by field_simp]
    exact div_nonneg (by nlinarith) hq'.le
  have hkey : a / c - 1 / p = (p * a - c) / (p * c) := by field_simp
  calc |a / c - 1 / p| = |p * a - c| / (p * c) := by
        rw [hkey, abs_div, abs_of_pos (show (0 : ℝ) < p * c by positivity)]
    _ ≤ (c / q) / (p * c) := by gcongr; exact abs_le.2 ⟨hlo, hup⟩
    _ = 1 / (p * q) := by field_simp

/-- `|c_{q,r} − p^{-1/2}| ≤ 1/(√p q)`. -/
theorem abs_logCellWeight_sub_le {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : r < p) :
    |Real.sqrt (logCell (q * p + r) / logCell q) - (Real.sqrt p)⁻¹| ≤ 1 / (Real.sqrt p * q) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp'
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (Real.sqrt p)⁻¹ = Real.sqrt (1 / p) by rw [Real.sqrt_div' 1 hp'.le, Real.sqrt_one, one_div]]
  refine (abs_sqrt_sub_sqrt_le_div (div_nonneg (logCell_nonneg _) (logCell_nonneg _))
    (by positivity)).trans ?_
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
  refine (abs_logCell_ratio_sub_le hp hq hr).trans (le_of_eq ?_)
  rw [Real.sqrt_div' 1 hp'.le, Real.sqrt_one]
  field_simp
  rw [Real.sq_sqrt hp'.le]

theorem divBlockMass_logCellWeight_sub_uniform_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    divBlockMass p (logCellWeight p - uniformWeight p) q ≤ 1 / (q : ℝ) ^ 2 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  calc divBlockMass p (logCellWeight p - uniformWeight p) q
      ≤ ∑ _r : Fin p, (1 / (Real.sqrt p * q)) ^ 2 := by
        refine Finset.sum_le_sum fun r _ => ?_
        simp only [Pi.sub_apply, logCellWeight, uniformWeight, div_block, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_logCellWeight_sub_le hp hq r.isLt) 2
    _ = 1 / (q : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow,
          mul_pow, Real.sq_sqrt hp'.le]
        field_simp

/-- **(2)** `W_p − V_p` is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_logCellShift_sub_uniformResidueShift {p : ℕ} (hp : 2 ≤ p) :
    ContinuousLinearMap.IsHilbertSchmidt (logCellShift p - uniformResidueShift p) := by
  have hp0 : 0 < p := by omega
  rw [logCellShift, uniformResidueShift, ← divBlockOp_sub hp0 (norm_logCellWeight_le_one hp)
    (fun _ => norm_uniformWeight_le hp0)]
  refine isHilbertSchmidt_divBlockOp hp0 (K := 1 + 1) (fun m =>
    (norm_sub_le _ _).trans (add_le_add (norm_logCellWeight_le_one hp m) (norm_uniformWeight_le hp0))) ?_
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun q => divBlockMass_nonneg _ _ _) (fun q => ?_)
    ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two))
  have hle := divBlockMass_logCellWeight_sub_uniform_le hp0 (Nat.succ_pos q)
  refine hle.trans (le_of_eq ?_)
  push_cast
  ring

/-! ### (3) The literal Euler channel is not a compact perturbation of translation -/

theorem tendsto_logCellWeight_block (p : ℕ) (hp : 0 < p) (r : ℕ) (hr : r < p) :
    Tendsto (fun q : ℕ => Real.sqrt (logCell (q * p + r) / logCell q)) atTop
      (𝓝 (Real.sqrt p)⁻¹) := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  have hlim : Tendsto (fun q : ℕ => 1 / (Real.sqrt p * q)) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (Real.sqrt p)⁻¹
    rw [mul_zero] at this
    refine this.congr fun q => ?_
    rw [one_div, one_div, mul_inv]
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hlim)
  filter_upwards [eventually_gt_atTop 0] with q hq
  rw [Real.norm_eq_abs]
  exact abs_logCellWeight_sub_le hp hq hr

theorem divBlockGram_label_logCellWeight {p : ℕ} (hp : 0 < p) (q : ℕ) :
    divBlockGram p (labelWeight p) (logCellWeight p) q = logCellWeight p (q * p) := by
  simp only [divBlockGram, labelWeight_block]
  rw [Finset.sum_eq_single ⟨0, hp⟩ (fun r _ hr => by simp [show (r : ℕ) ≠ 0 from fun h => hr (Fin.ext h)])
    (by simp)]
  simp

theorem divBlockMass_label_sub_logCellWeight {p : ℕ} (hp : 2 ≤ p) {q : ℕ} (hq : 0 < q) :
    divBlockMass p (labelWeight p - logCellWeight p) q =
      2 - 2 * Real.sqrt (logCell (q * p) / logCell q) := by
  have hp0 : 0 < p := by omega
  haveI : NeZero p := ⟨hp0.ne'⟩
  rw [divBlockMass_sub_eq, divBlockMass_labelWeight hp0, divBlockMass_logCellWeight hp0 hq,
    divBlockGram_label_logCellWeight hp0, logCellWeight,
    show q * p = q * p + ((⟨0, hp0⟩ : Fin p) : ℕ) by simp, div_block]
  simp only [Complex.ofReal_re, add_zero]
  ring

/-- **(3)** `‖S_p − W_p‖_ess = √(2 − 2/√p)`. -/
theorem essentialNorm_eulerLabelShift_sub_logCellShift {p : ℕ} (hp : 2 ≤ p) :
    essentialNorm (eulerLabelShift p - logCellShift p) = Real.sqrt (2 - 2 / Real.sqrt p) := by
  have hp0 : 0 < p := by omega
  have hsp : 1 ≤ Real.sqrt p := Real.one_le_sqrt.2 (by exact_mod_cast hp0)
  have hβ : 0 ≤ 2 - 2 / Real.sqrt p := by
    rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith
  rw [eulerLabelShift, logCellShift, ← divBlockOp_sub hp0 (norm_labelWeight_le p)
    (norm_logCellWeight_le_one hp)]
  refine essentialNorm_divBlockOp hp0 (K := 1 + 1) (fun m => (norm_sub_le _ _).trans
    (add_le_add (norm_labelWeight_le p m) (norm_logCellWeight_le_one hp m))) (Real.sqrt_nonneg _) ?_
  rw [Real.sq_sqrt hβ]
  have hc := tendsto_logCellWeight_block p hp0 0 hp0
  simp only [add_zero] at hc
  have hlim := (hc.const_mul 2).const_sub 2
  rw [show (2 : ℝ) - 2 * (Real.sqrt p)⁻¹ = 2 - 2 / Real.sqrt p by rw [div_eq_mul_inv]] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with q hq
  exact (divBlockMass_label_sub_logCellWeight hp hq).symm

/-! ### (4), (5) The residue channel -/

/-- `R_p = S_p − p^{-1/2} V_p`. -/
theorem residueChannel_eq {p : ℕ} (hp : 0 < p) :
    residueChannel p = eulerLabelShift p - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) • uniformResidueShift p := by
  have hsm : ∀ m, ‖((((Real.sqrt p)⁻¹ : ℝ) : ℂ) • uniformWeight p) m‖ ≤ 1 := fun m => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ (norm_uniformWeight_le hp) (norm_nonneg _) (norm_uniformWeight_le hp)
  rw [residueChannel, eulerLabelShift, uniformResidueShift, ← divBlockOp_smul hp
    (fun _ => norm_uniformWeight_le hp), ← divBlockOp_sub hp (norm_labelWeight_le p) hsm]
  congr 1
  funext m
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg p)]

/-- **(4a)** `V_p* R_p = 0`. -/
theorem adjoint_uniformResidueShift_comp_residueChannel {p : ℕ} (hp : 0 < p) :
    (uniformResidueShift p).adjoint ∘L residueChannel p = 0 := by
  rw [uniformResidueShift, residueChannel, adjoint_comp_divBlockOp hp
    (fun _ => norm_uniformWeight_le hp) (norm_residueChannelWeight_le hp) (κ := 0)
    (fun q _ => divBlockGram_uniform_residue hp q), zero_smul]

/-- **(4b)** `R_p* R_p = (1 − 1/p) I`. -/
theorem adjoint_residueChannel_comp_self {p : ℕ} (hp : 0 < p) :
    (residueChannel p).adjoint ∘L residueChannel p =
      (((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ ℓ²₊ := by
  rw [residueChannel, adjoint_comp_divBlockOp hp (norm_residueChannelWeight_le hp) (norm_residueChannelWeight_le hp)
    (fun q _ => divBlockGram_residue_self hp q)]

theorem norm_residueChannel_apply {p : ℕ} (hp : 0 < p) (f : ℓ²₊) :
    ‖residueChannel p f‖ = Real.sqrt (1 - (p : ℝ)⁻¹) * ‖f‖ := by
  have h := norm_sq_divBlockOp hp (norm_residueChannelWeight_le hp) f
  simp only [divBlockMass_residueChannelWeight hp] at h
  rw [tsum_mul_left, ← norm_sq_eq_tsum_extZero] at h
  have h1 : 0 ≤ 1 - (p : ℝ)⁻¹ := by
    rw [sub_nonneg]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hp)
  rw [← Real.sqrt_sq (norm_nonneg (residueChannel p f)), residueChannel, h, Real.sqrt_mul h1,
    Real.sqrt_sq (norm_nonneg _)]

/-- **(5)** `S_p = p^{-1/2} W_p + R_p` modulo Hilbert–Schmidt. -/
theorem isHilbertSchmidt_eulerLabelShift_sub {p : ℕ} (hp : 2 ≤ p) :
    ContinuousLinearMap.IsHilbertSchmidt
      (eulerLabelShift p - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) • logCellShift p - residueChannel p) := by
  have hp0 : 0 < p := by omega
  have heq : eulerLabelShift p - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) • logCellShift p - residueChannel p =
      -((((Real.sqrt p)⁻¹ : ℝ) : ℂ) • (logCellShift p - uniformResidueShift p)) := by
    rw [residueChannel_eq hp0, smul_sub]
    abel
  rw [heq]
  exact ((isHilbertSchmidt_logCellShift_sub_uniformResidueShift hp).smul _).neg

/-- The literal source shift `p^{-1/2} S_p` has residue part of norm `p^{-1/2} √(1 − 1/p)` on every
basis vector. -/
theorem norm_sourceShift_residue_single {p : ℕ} (hp : 0 < p) (n : ℕ+) :
    ‖(((Real.sqrt p)⁻¹ : ℝ) : ℂ) • residueChannel p (lp.single 2 n (1 : ℂ))‖ =
      (Real.sqrt p)⁻¹ * Real.sqrt (1 - (p : ℝ)⁻¹) := by
  rw [norm_smul, norm_residueChannel_apply hp, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    lp.norm_single (by norm_num), norm_one, mul_one]

/-! ### (6) Mixed curvature of the two transports -/

theorem logCellWeight_eq (p m : ℕ) : logCellWeight p m = ((Real.sqrt (logCell m / logCell (m / p)) : ℝ) : ℂ) :=
  rfl

theorem eulerLabelShift_comp_logCellShift {p : ℕ} (hp : 2 ≤ p) :
    eulerLabelShift p ∘L logCellShift p =
      divBlockOp (p * p) (fun m => labelWeight p m * logCellWeight p (m / p)) :=
  divBlockOp_comp (by omega) (by omega) (norm_labelWeight_le p) (norm_logCellWeight_le_one hp)

theorem logCellShift_comp_eulerLabelShift {p : ℕ} (hp : 2 ≤ p) :
    logCellShift p ∘L eulerLabelShift p =
      divBlockOp (p * p) (fun m => logCellWeight p m * labelWeight p (m / p)) :=
  divBlockOp_comp (by omega) (by omega) (norm_logCellWeight_le_one hp) (norm_labelWeight_le p)

theorem divBlockMass_eq_one_of_isometry {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ}
    (hw : ∀ m, ‖w m‖ ≤ K) (hiso : ∀ f, ‖divBlockOp b w f‖ = ‖f‖) {q : ℕ} (hq : 0 < q) :
    divBlockMass b w q = 1 := by
  have h := norm_sq_divBlockOp_single hb hw ⟨q, hq⟩
  rw [hiso, lp.norm_single (by norm_num), norm_one, one_pow] at h
  exact h.symm

theorem not_dvd_div_of_block {p q j : ℕ} (hp : 0 < p) (hj : j < p * p) (hj0 : j ≠ 0)
    (h1 : p ∣ q * (p * p) + j) : ¬ p ∣ (q * (p * p) + j) / p := by
  have hpj : p ∣ j := (Nat.dvd_add_right (dvd_mul_of_dvd_right (dvd_mul_left p p) q)).1 h1
  obtain ⟨t, rfl⟩ := hpj
  have ht : t < p := by
    by_contra h; push Not at h; nlinarith
  rw [show q * (p * p) + p * t = p * (q * p + t) by ring, Nat.mul_div_cancel_left _ hp]
  rw [Nat.dvd_add_right (dvd_mul_left p q)]
  intro hpt
  have : t = 0 := Nat.eq_zero_of_dvd_of_lt hpt ht
  subst this
  exact hj0 (by simp)

theorem divBlockGram_commutator {p : ℕ} (hp : 2 ≤ p) (q : ℕ) :
    divBlockGram (p * p) (fun m => labelWeight p m * logCellWeight p (m / p))
      (fun m => logCellWeight p m * labelWeight p (m / p)) q =
      logCellWeight p (q * p) * logCellWeight p (q * p * p) := by
  have hp0 : 0 < p := by omega
  have hpp : 0 < p * p := Nat.mul_pos hp0 hp0
  rw [divBlockGram, Finset.sum_eq_single (⟨0, hpp⟩ : Fin (p * p))]
  · simp only [add_zero, labelWeight]
    rw [if_pos (dvd_mul_of_dvd_right (dvd_mul_left p p) q),
      show q * (p * p) / p = q * p by rw [← mul_assoc, Nat.mul_div_cancel _ hp0],
      if_pos (dvd_mul_left p q), show q * (p * p) = q * p * p by ring]
    simp [logCellWeight]
  · intro j _ hj
    have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp only [labelWeight]
    by_cases h1 : p ∣ q * (p * p) + j
    · rw [if_neg (not_dvd_div_of_block hp0 j.isLt hj0 h1)]
      simp
    · rw [if_neg h1]
      simp
  · simp

/-- **(6)** `‖S_p W_p − W_p S_p‖_ess = √(2 − 2/p)`. -/
theorem essentialNorm_commutator_eulerLabelShift_logCellShift {p : ℕ} (hp : 2 ≤ p) :
    essentialNorm (eulerLabelShift p ∘L logCellShift p - logCellShift p ∘L eulerLabelShift p) =
      Real.sqrt (2 - 2 / p) := by
  have hp0 : 0 < p := by omega
  have hpp : 0 < p * p := Nat.mul_pos hp0 hp0
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hβ : 0 ≤ 2 - 2 / (p : ℝ) := by rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith
  have hw1 : ∀ m, ‖labelWeight p m * logCellWeight p (m / p)‖ ≤ 1 := fun m => by
    rw [norm_mul]; exact mul_le_one₀ (norm_labelWeight_le p m) (norm_nonneg _)
      (norm_logCellWeight_le_one hp _)
  have hw2 : ∀ m, ‖logCellWeight p m * labelWeight p (m / p)‖ ≤ 1 := fun m => by
    rw [norm_mul]; exact mul_le_one₀ (norm_logCellWeight_le_one hp m) (norm_nonneg _)
      (norm_labelWeight_le p _)
  rw [eulerLabelShift_comp_logCellShift hp, logCellShift_comp_eulerLabelShift hp,
    ← divBlockOp_sub hpp hw1 hw2]
  refine essentialNorm_divBlockOp hpp (K := 1 + 1) (fun m => (norm_sub_le _ _).trans
    (add_le_add (hw1 m) (hw2 m))) (Real.sqrt_nonneg _) ?_
  rw [Real.sq_sqrt hβ]
  have hiso1 : ∀ f, ‖divBlockOp (p * p) (fun m => labelWeight p m * logCellWeight p (m / p)) f‖ = ‖f‖ :=
    fun f => by
      rw [← eulerLabelShift_comp_logCellShift hp, ContinuousLinearMap.comp_apply,
        norm_eulerLabelShift_apply hp0, norm_logCellShift_apply hp]
  have hiso2 : ∀ f, ‖divBlockOp (p * p) (fun m => logCellWeight p m * labelWeight p (m / p)) f‖ = ‖f‖ :=
    fun f => by
      rw [← logCellShift_comp_eulerLabelShift hp, ContinuousLinearMap.comp_apply,
        norm_logCellShift_apply hp, norm_eulerLabelShift_apply hp0]
  have hmono : Tendsto (fun q : ℕ => q * p) atTop atTop :=
    tendsto_atTop_atTop.2 fun B => ⟨B, fun a ha => le_trans ha (Nat.le_mul_of_pos_right a hp0)⟩
  have hc1 : Tendsto (fun q : ℕ => Real.sqrt (logCell (q * p) / logCell q)) atTop
      (𝓝 (Real.sqrt p)⁻¹) := by
    simpa using tendsto_logCellWeight_block p hp0 0 hp0
  have hc2 : Tendsto (fun q : ℕ => Real.sqrt (logCell (q * p * p) / logCell (q * p))) atTop
      (𝓝 (Real.sqrt p)⁻¹) := hc1.comp hmono
  have hlim := ((hc1.mul hc2).const_mul 2).const_sub 2
  have hval : (2 : ℝ) - 2 * ((Real.sqrt p)⁻¹ * (Real.sqrt p)⁻¹) = 2 - 2 / p := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg p), div_eq_mul_inv]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with q hq
  rw [show (fun m => labelWeight p m * logCellWeight p (m / p) - logCellWeight p m * labelWeight p (m / p)) =
      (fun m => labelWeight p m * logCellWeight p (m / p)) -
        (fun m => logCellWeight p m * labelWeight p (m / p)) from rfl,
    divBlockMass_sub_eq, divBlockMass_eq_one_of_isometry hpp hw1 hiso1 hq,
    divBlockMass_eq_one_of_isometry hpp hw2 hiso2 hq, divBlockGram_commutator hp q, logCellWeight_eq,
    logCellWeight_eq, Nat.mul_div_cancel _ hp0, Nat.mul_div_cancel _ hp0, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

/-! ### (7) All prime residue channels are complete modulo the vacuum -/

/-- The unit (vacuum) vector `e_1`. -/
def vacuumVec : ℓ²₊ := lp.single 2 1 (1 : ℂ)

theorem coord_eq_inner_lpSingle (f : ℓ²₊) (n : ℕ+) :
    (f : ℕ+ → ℂ) n = inner ℂ (lp.single 2 n (1 : ℂ)) f := by
  classical
  rw [lp.inner_single_left, RCLike.inner_apply]
  simp

theorem inner_vacuumVec (f : ℓ²₊) : inner ℂ vacuumVec f = (f : ℕ+ → ℂ) 1 := by
  rw [vacuumVec, ← coord_eq_inner_lpSingle]

theorem mem_vacuum_orthogonal_iff (f : ℓ²₊) :
    f ∈ (ℂ ∙ vacuumVec)ᗮ ↔ (f : ℕ+ → ℂ) 1 = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_vacuumVec]

theorem conj_residueChannelWeight (p m : ℕ) : conj (residueChannelWeight p m) = residueChannelWeight p m := by
  simp [residueChannelWeight]

/-- `⟪R_p e_n, f⟫ = Σ_{r<p} ([r=0] − 1/p) f(np + r)`. -/
theorem inner_residueChannel_single {p : ℕ} (hp : 0 < p) (n : ℕ+) (f : ℓ²₊) :
    inner ℂ (residueChannel p (lp.single 2 n (1 : ℂ))) f =
      ∑ r : Fin p, residueChannelWeight p (n * p + r) * extZero f (n * p + r) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [inner_eq_tsum_ext]
  have hcoord : ∀ m, extZero (residueChannel p (lp.single 2 n (1 : ℂ))) m =
      residueChannelWeight p m * (if m / p = n then 1 else 0) := fun m => by
    rw [residueChannel, extZero_divBlockOp hp (norm_residueChannelWeight_le hp), extZero_single]
  simp_rw [hcoord]
  have hs : Summable fun m => conj (residueChannelWeight p m * (if m / p = (n : ℕ) then 1 else 0)) *
      extZero f m := by
    refine summable_of_ne_finset_zero (s := Finset.range ((n + 1) * p)) fun m hm => ?_
    have hne : m / p ≠ n := by
      intro h
      apply hm
      rw [Finset.mem_range]
      have := Nat.lt_mul_div_succ m hp
      rw [h] at this
      linarith [mul_comm p ((n : ℕ) + 1)]
    simp [hne]
  rw [tsum_block (b := p) hs, tsum_eq_single (n : ℕ)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [div_block, if_pos rfl, mul_one, conj_residueChannelWeight]
  · intro q hq
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [div_block, if_neg hq]
    simp

theorem adjoint_residueChannel_eq_zero_iff {p : ℕ} (hp : 0 < p) (f : ℓ²₊) :
    (residueChannel p).adjoint f = 0 ↔
      ∀ n : ℕ+, ∑ r : Fin p, residueChannelWeight p (n * p + r) * extZero f (n * p + r) = 0 := by
  constructor
  · intro h n
    rw [← inner_residueChannel_single hp, ← ContinuousLinearMap.adjoint_inner_right, h, inner_zero_right]
  · intro h
    ext n
    rw [coord_eq_inner_lpSingle, ContinuousLinearMap.adjoint_inner_right,
      inner_residueChannel_single hp, h n]
    rfl

theorem sum_residueChannelWeight_block {p : ℕ} (hp : 0 < p) (q : ℕ) (F : ℕ → ℂ) :
    ∑ r : Fin p, residueChannelWeight p (q * p + r) * F (q * p + r) =
      F (q * p) - (p : ℂ)⁻¹ * ∑ r : Fin p, F (q * p + r) := by
  have hsplit : ∀ r : Fin p, residueChannelWeight p (q * p + r) * F (q * p + r) =
      (if (r : ℕ) = 0 then F (q * p + r) else 0) - (p : ℂ)⁻¹ * F (q * p + r) := fun r => by
    simp only [residueChannelWeight, dvd_block_iff]
    split_ifs <;> push_cast <;> ring
  simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single ⟨0, hp⟩ (fun r _ hr => if_neg fun h => hr (Fin.ext h)) (by simp)]
  simp

/-- **(7) Vacuum rigidity.**  A vector killed by every `R_p*` (`p` prime) is supported at the unit. -/
theorem forall_adjoint_residueChannel_eq_zero_iff (f : ℓ²₊) :
    (∀ p : ℕ, p.Prime → (residueChannel p).adjoint f = 0) ↔
      ∀ n : ℕ+, n ≠ 1 → (f : ℕ+ → ℂ) n = 0 := by
  constructor
  · intro h n hn
    have hvac := highpass_prime_average_supported_at_one (extZero f) (extZero_zero f)
      (summable_norm_sq_extZero f) (fun p m hp hm => ?_) n (fun h1 => hn (PNat.eq h1))
    · simpa using hvac
    have hp0 := hp.pos
    have hz := (adjoint_residueChannel_eq_zero_iff hp0 f).1 (h p hp) ⟨m, hm⟩
    rw [sum_residueChannelWeight_block hp0] at hz
    simp only [PNat.mk_coe] at hz
    have hrange : ∑ r : Fin p, extZero f (m * p + r) =
        extZero f (m * p) + ∑ r ∈ Finset.Ico 1 p, extZero f (m * p + r) := by
      rw [Fin.sum_univ_eq_sum_range (fun r => extZero f (m * p + r)) p, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot hp0]
      simp
    rw [hrange] at hz
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [Nat.cast_sub hp.one_le, Nat.cast_one, mul_comm p m]
    field_simp at hz
    linear_combination hz
  · intro h p hp
    rw [adjoint_residueChannel_eq_zero_iff hp.pos]
    intro n
    refine Finset.sum_eq_zero fun r _ => ?_
    have hm : 1 < (n : ℕ) * p + r := by
      have := hp.two_le; have := n.pos; nlinarith
    have : extZero f (n * p + r) = 0 := by
      have hpos : 0 < (n : ℕ) * p + r := by omega
      rw [show extZero f (n * p + r) = (f : ℕ+ → ℂ) ⟨n * p + r, hpos⟩ by simp [extZero, hpos]]
      exact h _ (fun h1 => by
        have := congrArg PNat.val h1
        simp at this
        omega)
    rw [this, mul_zero]

theorem iInf_ker_adjoint_residueChannel :
    (⨅ p : Nat.Primes, LinearMap.ker ((residueChannel p).adjoint : ℓ²₊ →ₗ[ℂ] ℓ²₊)) = ℂ ∙ vacuumVec := by
  classical
  ext f
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Submodule.mem_span_singleton]
  constructor
  · intro h
    have hv := (forall_adjoint_residueChannel_eq_zero_iff f).1 fun p hp => h ⟨p, hp⟩
    refine ⟨(f : ℕ+ → ℂ) 1, ?_⟩
    ext n
    by_cases hn : n = 1
    · subst hn; simp [vacuumVec]
    · rw [hv n hn]; simp [vacuumVec, lp.single_apply, hn]
  · rintro ⟨a, rfl⟩ p
    refine (forall_adjoint_residueChannel_eq_zero_iff (a • vacuumVec)).2 (fun n hn => ?_) p p.prop
    simp [vacuumVec, lp.single_apply, hn]

/-- **(7)** `closure span{Ran R_p : p prime} = {f : f(1) = 0} = (ℂ e_1)^⊥`. -/
theorem topologicalClosure_iSup_range_residueChannel :
    (⨆ p : Nat.Primes, LinearMap.range (residueChannel p : ℓ²₊ →ₗ[ℂ] ℓ²₊)).topologicalClosure =
      (ℂ ∙ vacuumVec)ᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.iInf_orthogonal]
  simp_rw [ContinuousLinearMap.orthogonal_range]
  rw [iInf_ker_adjoint_residueChannel]

/-! ### The invariant hull of the prime vectors -/

theorem single_mem_vacuum_orthogonal {n : ℕ+} (hn : n ≠ 1) :
    lp.single 2 n (1 : ℂ) ∈ (ℂ ∙ vacuumVec)ᗮ := by
  classical
  rw [mem_vacuum_orthogonal_iff, lp.single_apply, Pi.single_apply, if_neg (Ne.symm hn)]

theorem eulerLabelShift_mem_vacuum_orthogonal {q : ℕ} (hq : 2 ≤ q) (f : ℓ²₊) :
    eulerLabelShift q f ∈ (ℂ ∙ vacuumVec)ᗮ := by
  rw [mem_vacuum_orthogonal_iff, eulerLabelShift, divBlockOp_apply (by omega) (norm_labelWeight_le q)]
  have h1 : ((1 : ℕ+) : ℕ) / q = 0 := Nat.div_eq_of_lt (by simp; omega)
  rw [h1, extZero_zero, mul_zero]

/-- **The invariant hull.**  Every closed subspace containing the prime basis vectors and invariant
under all `S_q`, `q` prime, contains `ℓ²(ℕ_{≥2}) = (ℂ e_1)^⊥`. -/
theorem vacuum_orthogonal_le {N : Submodule ℂ ℓ²₊} (hN : IsClosed (N : Set ℓ²₊))
    (hprime : ∀ p : ℕ+, (p : ℕ).Prime → lp.single 2 p (1 : ℂ) ∈ N)
    (hinv : ∀ q : ℕ, q.Prime → ∀ f ∈ N, eulerLabelShift q f ∈ N) :
    (ℂ ∙ vacuumVec)ᗮ ≤ N := by
  classical
  have hbasis : ∀ k : ℕ, ∀ n : ℕ+, (n : ℕ) = k → n ≠ 1 → lp.single 2 n (1 : ℂ) ∈ N := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hnk hn
      have hn1 : (n : ℕ) ≠ 1 := fun h => hn (PNat.eq h)
      by_cases hpr : (n : ℕ).Prime
      · exact hprime n hpr
      · set q := (n : ℕ).minFac
        have hq := Nat.minFac_prime hn1
        have hqn : q ∣ (n : ℕ) := Nat.minFac_dvd _
        have hk2 : 2 ≤ (n : ℕ) / q := by
          by_contra hlt
          push Not at hlt
          have hpos : 0 < (n : ℕ) / q := Nat.div_pos (Nat.minFac_le n.pos) hq.pos
          have h1 : (n : ℕ) / q = 1 := by omega
          have : (n : ℕ) = q := by
            rw [← Nat.mul_div_cancel' hqn, h1, mul_one]
          exact hpr (this ▸ hq)
        have hkpos : 0 < (n : ℕ) / q := by omega
        have hlt : (n : ℕ) / q < k := by
          rw [← hnk]; exact Nat.div_lt_self n.pos hq.one_lt
        have hmem := ih _ hlt ⟨(n : ℕ) / q, hkpos⟩ rfl (fun h => by
          have := congrArg PNat.val h; simp at this; omega)
        have hshift := hinv q hq _ hmem
        rw [eulerLabelShift_single hq.pos] at hshift
        convert hshift using 2
        apply PNat.eq
        rw [PNat.mul_coe, PNat.mk_coe, PNat.mk_coe, Nat.mul_div_cancel' hqn]
  intro f hf
  rw [mem_vacuum_orthogonal_iff] at hf
  have hsum := lp.hasSum_single (E := fun _ : ℕ+ => ℂ) (p := 2) (by norm_num) f
  refine hN.mem_of_tendsto hsum (Eventually.of_forall fun s => N.sum_mem fun n _ => ?_)
  by_cases hn : n = 1
  · subst hn; rw [hf, lp.single_zero]; exact N.zero_mem
  · convert N.smul_mem ((f : ℕ+ → ℂ) n) (hbasis _ n rfl hn) using 1
    ext m
    by_cases h : m = n
    · subst h; simp [lp.single_apply]
    · simp [lp.single_apply, h]

/-- Adding the vacuum gives the whole space. -/
theorem vacuum_orthogonal_sup_span : (ℂ ∙ vacuumVec)ᗮ ⊔ (ℂ ∙ vacuumVec) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun f => ?_
  have h1 : f - (f : ℕ+ → ℂ) 1 • vacuumVec ∈ (ℂ ∙ vacuumVec)ᗮ := by
    rw [mem_vacuum_orthogonal_iff]
    simp [vacuumVec]
  have h2 : (f : ℕ+ → ℂ) 1 • vacuumVec ∈ ℂ ∙ vacuumVec := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  simpa using Submodule.add_mem_sup h1 h2

/-- The closed span of the prime vectors is not invariant under Euler multiplication:
`S_2 e_2 = e_4` lies outside it. -/
theorem eulerLabelShift_two_not_mem_primeSpan :
    eulerLabelShift 2 (lp.single 2 2 (1 : ℂ)) ∉
      (Submodule.span ℂ (Set.range fun p : {n : ℕ+ // (n : ℕ).Prime} =>
        lp.single 2 (p : ℕ+) (1 : ℂ))).topologicalClosure := by
  classical
  have h4 : eulerLabelShift 2 (lp.single 2 2 (1 : ℂ)) = (lp.single 2 (4 : ℕ+) (1 : ℂ) : ℓ²₊) := by
    rw [eulerLabelShift_single (by norm_num)]
    rfl
  have hle : (Submodule.span ℂ (Set.range fun p : {n : ℕ+ // (n : ℕ).Prime} =>
      lp.single 2 (p : ℕ+) (1 : ℂ))).topologicalClosure ≤
        (ℂ ∙ (lp.single 2 (4 : ℕ+) (1 : ℂ) : ℓ²₊))ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
      ← coord_eq_inner_lpSingle, lp.single_apply, Pi.single_apply, if_neg]
    intro h
    have : ((4 : ℕ+) : ℕ).Prime := h ▸ p.prop
    norm_num at this
  intro hmem
  have := hle hmem
  rw [h4, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at this
  simpa using congrArg (fun g : ℓ²₊ => (g : ℕ+ → ℂ) 4) this

section CellClock

open MeasureTheory Set GaloisForLFunctions.HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### Two continuous linear maps agreeing on the basis agree -/

theorem lpSingle_eq_smul_one (n : ℕ+) (c : ℂ) :
    (lp.single 2 n c : ℓ²₊) = c • lp.single 2 n (1 : ℂ) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

theorem clm_ext_single {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T S : ℓ²₊ →L[ℂ] F} (h : ∀ n : ℕ+, T (lp.single 2 n (1 : ℂ)) = S (lp.single 2 n (1 : ℂ))) :
    T = S := by
  classical
  ext1 f
  have hsum := lp.hasSum_single (E := fun _ : ℕ+ => ℂ) (p := 2) (by norm_num) f
  have hcol : ∀ n, T (lp.single 2 n ((f : ℕ+ → ℂ) n)) = S (lp.single 2 n ((f : ℕ+ → ℂ) n)) :=
    fun n => by rw [lpSingle_eq_smul_one, map_smul, map_smul, h]
  have h1 := hsum.mapL T
  have h2 := hsum.mapL S
  simp only [hcol] at h1
  exact h1.unique h2

theorem coord_sum_smul_single {b : ℕ} (a : Fin b → ℂ) (idx : Fin b → ℕ+) (m : ℕ+) :
    ((∑ r : Fin b, a r • lp.single 2 (idx r) (1 : ℂ) : ℓ²₊) : ℕ+ → ℂ) m =
      ∑ r : Fin b, a r * (if m = idx r then 1 else 0) := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
    Pi.single_apply, smul_eq_mul]

theorem divBlockOp_single_eq_sum {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (n : ℕ+) : divBlockOp b w (lp.single 2 n (1 : ℂ)) =
      ∑ r : Fin b, w (n * b + r) • lp.single 2 (Nat.toPNat (n * b + r) (by have := n.pos; positivity)) (1 : ℂ) := by
  classical
  haveI : NeZero b := ⟨hb.ne'⟩
  ext m
  rw [divBlockOp_single_apply hb hw]
  erw [coord_sum_smul_single]
  by_cases hmn : (m : ℕ) / b = n
  · have hm : (m : ℕ) = n * b + (m : ℕ) % b := by
      rw [← hmn, mul_comm]; exact (Nat.div_add_mod _ _).symm
    rw [if_pos hmn, Finset.sum_eq_single ⟨(m : ℕ) % b, Nat.mod_lt _ hb⟩]
    · rw [if_pos (PNat.eq hm), mul_one]
      congr 1
    · intro r _ hr
      rw [if_neg, mul_zero]
      intro h
      apply hr
      apply Fin.ext
      have h' : (m : ℕ) = n * b + r := congrArg PNat.val h
      have hmod : (m : ℕ) % b = r := by
        rw [h', show (n : ℕ) * b + r = r + b * n by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt r.isLt]
      simp only [hmod]
    · simp
  · rw [if_neg hmn]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    rw [if_neg, mul_zero]
    intro h
    apply hmn
    have h' : (m : ℕ) = n * b + r := congrArg PNat.val h
    rw [h', div_block]

/-! ### The logarithmic cell clock and its translations -/

/-- The logarithmic cell `I_n = [log n, log(n+1))`. -/
def logCellSet (n : ℕ+) : Set ℝ := Ico (Real.log n) (Real.log ((n : ℕ) + 1))

theorem logCellSet_subset (n : ℕ+) : logCellSet n ⊆ Ici 0 := fun _ hx =>
  le_trans (Real.log_nonneg (Nat.one_le_cast.2 n.pos)) hx.1

theorem halfLineMeasure_logCellSet (n : ℕ+) :
    halfLineMeasure (logCellSet n) = ENNReal.ofReal (logCell n) := by
  have hsub := logCellSet_subset n
  unfold logCellSet at hsub ⊢
  rw [halfLineMeasure, Measure.restrict_apply measurableSet_Ico, inter_eq_left.2 hsub,
    Real.volume_Ico, logCell]

theorem halfLineMeasure_logCellSet_ne_top (n : ℕ+) : halfLineMeasure (logCellSet n) ≠ ⊤ := by
  rw [halfLineMeasure_logCellSet]; exact ENNReal.ofReal_ne_top

theorem halfLineMeasure_logCellSet_ne_zero (n : ℕ+) : halfLineMeasure (logCellSet n) ≠ 0 := by
  rw [halfLineMeasure_logCellSet, ENNReal.ofReal_ne_zero_iff]  
  exact logCell_pos n.pos

theorem pairwise_disjoint_logCellSet : Pairwise (Function.onFun Disjoint logCellSet) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · have hle : ((n : ℕ) : ℝ) + 1 ≤ (m : ℕ) := by exact_mod_cast (show (n : ℕ) + 1 ≤ m from h)
    have := Real.log_le_log (by positivity) hle
    linarith
  · have hle : ((m : ℕ) : ℝ) + 1 ≤ (n : ℕ) := by exact_mod_cast (show (m : ℕ) + 1 ≤ n from h)
    have := Real.log_le_log (by positivity) hle
    linarith

/-- The normalized cell vector `U e_n = 1_{I_n}/√ℓ_n`. -/
def logCellVec (n : ℕ+) : L²₊ :=
  SchurKernel.cellVec logCellSet (fun _ => measurableSet_Ico) halfLineMeasure_logCellSet_ne_top n

theorem orthonormal_logCellVec : Orthonormal ℂ logCellVec :=
  SchurKernel.orthonormal_cellVec logCellSet (fun _ => measurableSet_Ico)
    halfLineMeasure_logCellSet_ne_top halfLineMeasure_logCellSet_ne_zero pairwise_disjoint_logCellSet

/-- The cell isometry `U : ℓ²(ℕ₊) → L²(0,∞)`. -/
def logCellIsometry : ℓ²₊ →ₗᵢ[ℂ] L²₊ := orthonormal_logCellVec.orthogonalFamily.linearIsometry

/-- The cell isometry as a bounded operator. -/
def logCellEmbedding : ℓ²₊ →L[ℂ] L²₊ := logCellIsometry.toContinuousLinearMap

theorem logCellEmbedding_single (n : ℕ+) :
    logCellEmbedding (lp.single 2 n (1 : ℂ)) = logCellVec n := by
  classical
  rw [logCellEmbedding, LinearIsometry.coe_toContinuousLinearMap, logCellIsometry,
    OrthogonalFamily.linearIsometry_apply_single]
  simp

theorem norm_logCellEmbedding_apply (f : ℓ²₊) : ‖logCellEmbedding f‖ = ‖f‖ :=
  logCellIsometry.norm_map f

theorem adjoint_logCellEmbedding_comp :
    logCellEmbedding.adjoint ∘L logCellEmbedding = ContinuousLinearMap.id ℂ ℓ²₊ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self logCellEmbedding).mp norm_logCellEmbedding_apply

theorem cellConst_logCellSet (n : ℕ+) :
    SchurKernel.cellConst (μ := halfLineMeasure) logCellSet n = logCell n ^ (-(1 / 2 : ℝ)) := by
  rw [SchurKernel.cellConst, halfLineMeasure_logCellSet, ENNReal.toReal_ofReal (logCell_nonneg _)]

theorem logCellVec_coeFn (n : ℕ+) :
    (logCellVec n : ℝ → ℂ) =ᵐ[halfLineMeasure]
      (logCellSet n).indicator (fun _ => ((logCell n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  rw [← cellConst_logCellSet]
  unfold logCellVec SchurKernel.cellVec
  exact indicatorConstLp_coeFn

theorem halfLineExtend_logCellVec (n : ℕ+) :
    (halfLineExtend (logCellVec n) : ℝ → ℂ) =ᵐ[volume]
      (logCellSet n).indicator (fun _ => ((logCell n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  refine (halfLineExtend_coeFn _).trans ?_
  refine (indicator_ae_eq_of_halfLine (logCellVec_coeFn n)).trans (Eventually.of_forall fun x => ?_)
  rw [Set.indicator_indicator, inter_eq_right.2 (logCellSet_subset n)]

/-- Right translation `(T_a f)(x) = f(x − a)` on the half-line (extended by zero). -/
def halfLineRightShift (a : ℝ) : L²₊ →L[ℂ] L²₊ :=
  halfLineRestrict ∘L (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - a)
    (measurePreserving_sub_right volume a)).toContinuousLinearMap ∘L halfLineExtend

theorem halfLineRightShift_coeFn (a : ℝ) (u : L²₊) :
    (halfLineRightShift a u : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (halfLineExtend u : ℝ → ℂ) (x - a) := by
  refine (halfLineRestrict_coeFn _).trans (ae_restrict_of_ae ?_)
  exact Lp.coeFn_compMeasurePreserving _ _

@[simp] theorem coe_toPNat (n : ℕ) (h : 0 < n) : ((n.toPNat h : ℕ+) : ℕ) = n := rfl

/-- Consecutive cells tile a translated cell: `[log m, log(m+k)) = ⋃_{r<k} I_{m+r}`. -/
theorem indicator_Ico_log_eq_sum {m : ℕ} (hm : 0 < m) (k : ℕ) (c : ℂ) (x : ℝ) :
    (Ico (Real.log m) (Real.log ((m + k : ℕ) : ℝ))).indicator (fun _ => c) x =
      ∑ r ∈ Finset.range k,
        (logCellSet (Nat.toPNat (m + r) (by omega))).indicator (fun _ => c) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : Real.log m ≤ Real.log ((m + k : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast (by omega : m ≤ m + k))
    have h2 : Real.log ((m + k : ℕ) : ℝ) ≤ Real.log ((m + (k + 1) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < m + k))
        (by exact_mod_cast (by omega : m + k ≤ m + (k + 1)))
    rw [← Set.Ico_union_Ico_eq_Ico h1 h2, Set.indicator_union_of_disjoint Set.Ico_disjoint_Ico_same]
    simp only [logCellSet, coe_toPNat]
    push_cast
    ring_nf

theorem coeFn_finset_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (v : ι → L²₊) :
    ((∑ i ∈ s, a i • v i : L²₊) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => ∑ i ∈ s, a i * (v i : ℝ → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (a i • v i) (∑ j ∈ s, a j • v j), Lp.coeFn_smul (a i) (v i), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

theorem sqrt_div_mul_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * a ^ (-(1 / 2 : ℝ)) = b ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow ha.le hb.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have h1 : 0 < a ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have h2 : 0 < b ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hb _
  field_simp

/-- **(1) Exact pullback.**  Translating a cell by `log p` gives the `W_p`-image:
`T_{log p} U e_n = Σ_{r<p} c_{n,r} U e_{np+r}`. -/
theorem halfLineRightShift_logCellVec {p : ℕ} (hp : 2 ≤ p) (n : ℕ+) :
    halfLineRightShift (Real.log p) (logCellVec n) =
      ∑ r : Fin p, logCellWeight p (n * p + r) •
        logCellVec (Nat.toPNat (n * p + r) (by have := n.pos; positivity)) := by
  have hp0 : 0 < p := by omega
  haveI : NeZero p := ⟨hp0.ne'⟩
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hn' : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  refine Lp.ext ?_
  have hL : (halfLineRightShift (Real.log p) (logCellVec n) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (logCellSet n).indicator (fun _ => ((logCell n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (x - Real.log p) := by
    refine (halfLineRightShift_coeFn _ _).trans (ae_restrict_of_ae ?_)
    exact (measurePreserving_sub_right volume (Real.log p)).quasiMeasurePreserving.ae_eq_comp
      (halfLineExtend_logCellVec n)
  have hR := coeFn_finset_sum_smul Finset.univ (fun r : Fin p => logCellWeight p (n * p + r))
    (fun r : Fin p => logCellVec (Nat.toPNat (n * p + r) (by have := n.pos; positivity)))
  have hR2 : ∀ᵐ x ∂halfLineMeasure, ∀ r : Fin p,
      (logCellVec (Nat.toPNat (n * p + r) (by have := n.pos; positivity)) : ℝ → ℂ) x =
        (logCellSet (Nat.toPNat (n * p + r) (by have := n.pos; positivity))).indicator
          (fun _ => ((logCell (n * p + r) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) x :=
    ae_all_iff.2 fun r => logCellVec_coeFn _
  filter_upwards [hL, hR, hR2] with x h1 h2 h3
  rw [h1, h2]
  simp_rw [h3]
  have hshift : (logCellSet n).indicator (fun _ => ((logCell n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (x - Real.log p) = (Ico (Real.log ((n : ℕ) * p : ℕ)) (Real.log (((n : ℕ) * p + p : ℕ) : ℝ))).indicator
        (fun _ => ((logCell n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) x := by
    simp only [Set.indicator_apply, logCellSet, mem_Ico]
    have e1 : Real.log (((n : ℕ) * p : ℕ) : ℝ) = Real.log (n : ℕ) + Real.log p := by
      push_cast; exact Real.log_mul hn'.ne' hp'.ne'
    have e2 : Real.log ((((n : ℕ) * p + p : ℕ)) : ℝ) = Real.log ((n : ℕ) + 1) + Real.log p := by
      rw [show (((n : ℕ) * p + p : ℕ) : ℝ) = ((n : ℕ) + 1) * p by push_cast; ring]
      exact Real.log_mul (by positivity) hp'.ne'
    rw [e1, e2]
    congr 1
    apply propext
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hshift, indicator_Ico_log_eq_sum (Nat.mul_pos n.pos hp0) p, ← Fin.sum_univ_eq_sum_range
    (fun r => (logCellSet (Nat.toPNat ((n : ℕ) * p + r) (by have := n.pos; positivity))).indicator
      (fun _ => ((logCell n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) x)]
  refine Finset.sum_congr rfl fun r _ => ?_
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs
  · rw [logCellWeight, div_block, ← Complex.ofReal_mul, sqrt_div_mul_rpow
      (logCell_pos (by have := n.pos; positivity)) (logCell_pos n.pos)]
  · rw [mul_zero]

/-- **(1) The step-function subspace is translation invariant, with pullback `W_p`**:
`T_{log p} U = U W_p`. -/
theorem halfLineRightShift_comp_logCellEmbedding {p : ℕ} (hp : 2 ≤ p) :
    halfLineRightShift (Real.log p) ∘L logCellEmbedding = logCellEmbedding ∘L logCellShift p := by
  refine clm_ext_single fun n => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, logCellEmbedding_single,
    halfLineRightShift_logCellVec hp, logCellShift,
    divBlockOp_single_eq_sum (by omega) (norm_logCellWeight_le_one hp)]
  simp only [map_sum, map_smul, logCellEmbedding_single]

/-- **(1)** `W_p = U* T_{log p} U`. -/
theorem logCellShift_eq_adjoint_comp {p : ℕ} (hp : 2 ≤ p) :
    logCellShift p = logCellEmbedding.adjoint ∘L halfLineRightShift (Real.log p) ∘L logCellEmbedding := by
  rw [halfLineRightShift_comp_logCellEmbedding hp, ← ContinuousLinearMap.comp_assoc,
    adjoint_logCellEmbedding_comp, ContinuousLinearMap.id_comp]

/-- **(1)** `U(H)` is invariant under `T_{log p}`. -/
theorem halfLineRightShift_mem_range_logCellEmbedding {p : ℕ} (hp : 2 ≤ p) (f : ℓ²₊) :
    halfLineRightShift (Real.log p) (logCellEmbedding f) ∈
      LinearMap.range (logCellEmbedding : ℓ²₊ →ₗ[ℂ] L²₊) :=
  ⟨logCellShift p f, by
    change logCellEmbedding (logCellShift p f) = _
    rw [← ContinuousLinearMap.comp_apply, ← halfLineRightShift_comp_logCellEmbedding hp,
      ContinuousLinearMap.comp_apply]⟩

end CellClock

end

end RHTower
