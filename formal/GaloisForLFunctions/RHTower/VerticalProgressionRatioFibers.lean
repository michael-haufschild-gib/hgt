import GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion

/-!
# Fibres of the quadruple ratio

A quadruple `q = (P, h, k)` (`m = P₁ + 1`, `n = P₂ + 1`) has frequency `λ_q = log(nk/(mh))`. Its
reduced ratio is the coprime pair `(a, b)` with `nk/(mh) = a/b` (`quadRatio`).

* **Fibres** (`setOf_quadRatio_eq`): for coprime `a, b ≥ 1` and fixed `h, k`, the quadruples of
  ratio `a/b` are `m = (j+1)kb/g`, `n = (j+1)ha/g`, `g = (ha, kb)`, `j ≥ 0`.
* **The fibre identity** (`tsum_fiber_quadPoint`, `sum_fiber_quadPoint`):
  `Σ_{h,k} Σ_{q of ratio a/b} c_q V(2πmn/t) e^{itλ_q} = (ab)^{−1/2} e^{it log(a/b)} F(a,b,t)`,
  since `(mn)^{−1/2} = g/((j+1)√(hakb))`, `2πmn/t = (j+1)²/x_{hk}(t)` and
  `Σ_j (j+1)^{−1} V((j+1)²/x) = 𝓗(x)`. The same computation with `|V|` gives the majorant form
  (`tsum_fiber_quadPoint_norm`) with `𝓗⁺(x) = Σ_j (j+1)^{−1}|V((j+1)²/x)|`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)
open ZetaGateProductAFE (diagIndex)

/-- The reduced ratio `nk/(mh)` of a quadruple as a pair of coprime naturals. -/
def quadRatio (P : ℕ × ℕ) (h k : ℕ) : ℕ × ℕ :=
  ((P.2 + 1) * k / Nat.gcd ((P.2 + 1) * k) ((P.1 + 1) * h),
    (P.1 + 1) * h / Nat.gcd ((P.2 + 1) * k) ((P.1 + 1) * h))

/-- Equal reduced fractions: if `x b = y a` with `(x,y) = (a,b) = 1`, then `x = a`, `y = b`. -/
theorem eq_of_coprime_of_mul_eq {x y a b : ℕ} (hxy : Nat.Coprime x y) (hab : Nat.Coprime a b)
    (ha : 0 < a) (h : x * b = y * a) : x = a ∧ y = b := by
  have h1 : x ∣ a := hxy.dvd_of_dvd_mul_left ⟨b, h.symm⟩
  have h2 : a ∣ x := hab.dvd_of_dvd_mul_right ⟨y, by rw [h]; ring⟩
  have hxa := Nat.dvd_antisymm h1 h2
  refine ⟨hxa, ?_⟩
  subst hxa
  exact (Nat.eq_of_mul_eq_mul_right ha (by rw [← h]; ring)).symm

theorem quadRatio_eq_iff {P : ℕ × ℕ} {h k a b : ℕ} (hk : 0 < k)
    (hab : Nat.Coprime a b) (ha : 0 < a) :
    quadRatio P h k = (a, b) ↔ (P.1 + 1) * (h * a) = (P.2 + 1) * (k * b) := by
  set x := (P.2 + 1) * k with hx
  set y := (P.1 + 1) * h with hy
  have hx0 : 0 < x := Nat.mul_pos (Nat.succ_pos _) hk
  set d := Nat.gcd x y with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ hx0
  have hxd : x = d * (x / d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)).symm
  have hyd : y = d * (y / d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)).symm
  have hcop : Nat.Coprime (x / d) (y / d) := Nat.coprime_div_gcd_div_gcd hd0
  unfold quadRatio
  rw [← hx, ← hy, ← hd, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    have : x * b = y * a := by rw [hxd, hyd, h1, h2]; ring
    calc (P.1 + 1) * (h * a) = y * a := by rw [hy]; ring
      _ = x * b := this.symm
      _ = (P.2 + 1) * (k * b) := by rw [hx]; ring
  · intro heq
    have h1 : x * b = y * a := by
      calc x * b = (P.2 + 1) * (k * b) := by rw [hx]; ring
        _ = (P.1 + 1) * (h * a) := heq.symm
        _ = y * a := by rw [hy]; ring
    have h2 : (x / d) * b = (y / d) * a := by
      apply Nat.eq_of_mul_eq_mul_left hd0
      calc d * (x / d * b) = d * (x / d) * b := by ring
        _ = x * b := by rw [← hxd]
        _ = y * a := h1
        _ = d * (y / d) * a := by rw [← hyd]
        _ = d * (y / d * a) := by ring
    exact eq_of_coprime_of_mul_eq hcop hab ha h2

/-- The reduced pair of the twisted gcd: `h' = ha/g`, `k' = kb/g`, `g = (ha, kb)`. -/
theorem fiber_params {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) :
    0 < h * a / Nat.gcd (h * a) (k * b) ∧ 0 < k * b / Nat.gcd (h * a) (k * b) ∧
      Nat.Coprime (h * a / Nat.gcd (h * a) (k * b)) (k * b / Nat.gcd (h * a) (k * b)) := by
  have hg : 0 < Nat.gcd (h * a) (k * b) := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh ha)
  exact ⟨Nat.div_pos (Nat.gcd_le_left _ (Nat.mul_pos hh ha)) hg,
    Nat.div_pos (Nat.gcd_le_right _ (Nat.mul_pos hk hb)) hg, Nat.coprime_div_gcd_div_gcd hg⟩

/-- **The fibre of `a/b`** is the diagonal ray of the reduced pair `(ha/g, kb/g)`. -/
theorem setOf_quadRatio_eq {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k) (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) :
    {P : ℕ × ℕ | quadRatio P h k = (a, b)} =
      Set.range (diagIndex (h * a / Nat.gcd (h * a) (k * b)) (k * b / Nat.gcd (h * a) (k * b))) := by
  obtain ⟨hh', hk', hcop⟩ := fiber_params hh hk ha hb
  rw [ZetaGateProductAFE.range_diagIndex hh' hk' hcop]
  ext P
  simp only [Set.mem_setOf_eq]
  rw [quadRatio_eq_iff hk hab ha]
  set g := Nat.gcd (h * a) (k * b)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh ha)
  have e1 : h * a = g * (h * a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have e2 : k * b = g * (k * b / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  constructor
  · intro heq
    apply Nat.eq_of_mul_eq_mul_left hg
    calc g * ((P.1 + 1) * (h * a / g)) = (P.1 + 1) * (g * (h * a / g)) := by ring
      _ = (P.1 + 1) * (h * a) := by rw [← e1]
      _ = (P.2 + 1) * (k * b) := heq
      _ = (P.2 + 1) * (g * (k * b / g)) := by rw [← e2]
      _ = g * ((P.2 + 1) * (k * b / g)) := by ring
  · intro heq
    calc (P.1 + 1) * (h * a) = (P.1 + 1) * (g * (h * a / g)) := by rw [← e1]
      _ = g * ((P.1 + 1) * (h * a / g)) := by ring
      _ = g * ((P.2 + 1) * (k * b / g)) := by rw [heq]
      _ = (P.2 + 1) * (g * (k * b / g)) := by ring
      _ = (P.2 + 1) * (k * b) := by rw [← e2]

/-! ## The fibre identity -/

theorem reduced_cast {h k a b : ℕ} (hh : 0 < h) (ha : 0 < a) :
    ((h * a / Nat.gcd (h * a) (k * b) : ℕ) : ℝ) =
      (h : ℝ) * a / (Nat.gcd (h * a) (k * b) : ℝ) := by
  have hg : (Nat.gcd (h * a) (k * b) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh ha)).ne'
  rw [Nat.cast_div (Nat.gcd_dvd_left _ _) hg]
  push_cast; ring

theorem reduced_cast' {h k a b : ℕ} (hh : 0 < h) (ha : 0 < a) :
    ((k * b / Nat.gcd (h * a) (k * b) : ℕ) : ℝ) =
      (k : ℝ) * b / (Nat.gcd (h * a) (k * b) : ℝ) := by
  have hg : (Nat.gcd (h * a) (k * b) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh ha)).ne'
  rw [Nat.cast_div (Nat.gcd_dvd_right _ _) hg]
  push_cast; ring

/-- The amplitude on the fibre: `(m n)^{−1/2} (hk)^{−1/2} = (ab)^{−1/2} (ha,kb)/(hk) · (j+1)^{−1}`. -/
theorem fiber_amp {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    pairAmp (diagIndex (h * a / Nat.gcd (h * a) (k * b)) (k * b / Nat.gcd (h * a) (k * b)) j) *
        ((Real.sqrt h)⁻¹ * (Real.sqrt k)⁻¹) =
      (Real.sqrt ((a : ℝ) * b))⁻¹ *
        ((Nat.gcd (h * a) (k * b) : ℝ) / ((h : ℝ) * k)) * ((j : ℝ) + 1)⁻¹ := by
  obtain ⟨hh', hk', _⟩ := fiber_params hh hk ha hb
  rw [ZetaNotch.pairAmp_diagIndex hh' hk', reduced_cast hh ha, reduced_cast' hh ha]
  have hg : (0 : ℝ) < (Nat.gcd (h * a) (k * b) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (k * b) (Nat.mul_pos hh ha)
  set g : ℝ := (Nat.gcd (h * a) (k * b) : ℝ)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsq : Real.sqrt ((h : ℝ) * a / g * ((k : ℝ) * b / g)) * Real.sqrt h * Real.sqrt k =
      (h : ℝ) * k / g * Real.sqrt ((a : ℝ) * b) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
      show (h : ℝ) * a / g * ((k : ℝ) * b / g) * h * k = ((h : ℝ) * k / g) ^ 2 * ((a : ℝ) * b) by
        field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hpos2 : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.mpr (by positivity)
  calc (Real.sqrt ((h : ℝ) * a / g * ((k : ℝ) * b / g)))⁻¹ * ((j : ℝ) + 1)⁻¹ *
        ((Real.sqrt h)⁻¹ * (Real.sqrt k)⁻¹)
      = (Real.sqrt ((h : ℝ) * a / g * ((k : ℝ) * b / g)) * Real.sqrt h * Real.sqrt k)⁻¹ *
          ((j : ℝ) + 1)⁻¹ := by rw [mul_inv, mul_inv]; ring
    _ = ((h : ℝ) * k / g * Real.sqrt ((a : ℝ) * b))⁻¹ * ((j : ℝ) + 1)⁻¹ := by rw [hsq]
    _ = _ := by field_simp

/-- The cutoff argument on the fibre: `2πmn/t = (j+1)²/x_{hk}(t)`. -/
theorem fiber_arg {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) {t : ℝ}
    (ht : 0 < t) (j : ℕ) :
    2 * Real.pi * pairProd (diagIndex (h * a / Nat.gcd (h * a) (k * b))
        (k * b / Nat.gcd (h * a) (k * b)) j) / t = ((j : ℝ) + 1) ^ 2 / ratioArg a b h k t := by
  obtain ⟨hh', hk', _⟩ := fiber_params hh hk ha hb
  rw [ZetaNotch.pairProd_diagIndex hh' hk', reduced_cast hh ha, reduced_cast' hh ha]
  unfold ratioArg
  have hg : (0 : ℝ) < (Nat.gcd (h * a) (k * b) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (k * b) (Nat.mul_pos hh ha)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  field_simp

/-- The frequency on the fibre: `λ = log a − log b`. -/
theorem fiber_freq {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    quadFreq (diagIndex (h * a / Nat.gcd (h * a) (k * b)) (k * b / Nat.gcd (h * a) (k * b)) j) h k =
      Real.log a - Real.log b := by
  obtain ⟨hh', hk', _⟩ := fiber_params hh hk ha hb
  unfold quadFreq
  rw [ZetaNotch.pairFreq_diagIndex hh' hk', reduced_cast hh ha, reduced_cast' hh ha]
  have hg : (0 : ℝ) < (Nat.gcd (h * a) (k * b) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (k * b) (Nat.mul_pos hh ha)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.log_div (by positivity) hg.ne', Real.log_div (by positivity) hg.ne',
    Real.log_mul hhR.ne' haR.ne', Real.log_mul hkR.ne' hbR.ne']
  ring

/-- **The fibre identity** for a fixed pair `(h, k)`. -/
theorem tsum_fiber_quadPoint (N : ℕ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = (a, b)}, (quadCoeff N P h k : ℂ) *
        smoothAFECutoff (2 * Real.pi * pairProd P / t) *
          Complex.exp ((t * quadFreq P h k : ℝ) * I) =
      ((Real.sqrt ((a : ℝ) * b))⁻¹ : ℂ) * Complex.exp ((t * (Real.log a - Real.log b) : ℝ) * I) *
        ((ratioWeight N a b h k : ℂ) * ZetaNotch.diagHarm (ratioArg a b h k t)) := by
  obtain ⟨hh', hk', hcop⟩ := fiber_params hh hk ha hb
  rw [setOf_quadRatio_eq hh hk hab ha hb,
    tsum_range (fun P : ℕ × ℕ => (quadCoeff N P h k : ℂ) *
      smoothAFECutoff (2 * Real.pi * pairProd P / t) * Complex.exp ((t * quadFreq P h k : ℝ) * I))
      (ZetaGateProductAFE.diagIndex_injective hk')]
  unfold ZetaNotch.diagHarm
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [fiber_arg hh hk ha hb ht j, fiber_freq hh hk ha hb j]
  have hamp := fiber_amp hh hk ha hb j
  unfold quadCoeff mollAmp ratioWeight
  have e : pairAmp (diagIndex (h * a / Nat.gcd (h * a) (k * b))
        (k * b / Nat.gcd (h * a) (k * b)) j) * (Sieve.linearMollifierCoeff N h / Real.sqrt h) *
        (Sieve.linearMollifierCoeff N k / Real.sqrt k) =
      (Real.sqrt ((a : ℝ) * b))⁻¹ * (Sieve.linearMollifierCoeff N h *
        Sieve.linearMollifierCoeff N k * (Nat.gcd (h * a) (k * b) : ℝ) / ((h : ℝ) * k)) *
          ((j : ℝ) + 1)⁻¹ := by
    rw [div_eq_mul_inv _ (Real.sqrt h), div_eq_mul_inv _ (Real.sqrt k)]
    calc _ = pairAmp (diagIndex (h * a / Nat.gcd (h * a) (k * b))
          (k * b / Nat.gcd (h * a) (k * b)) j) * ((Real.sqrt h)⁻¹ * (Real.sqrt k)⁻¹) *
            (Sieve.linearMollifierCoeff N h * Sieve.linearMollifierCoeff N k) := by ring
      _ = _ := by rw [hamp]; ring
  rw [e]
  push_cast
  ring

/-! ## Fibre decomposition of the expansion -/

/-- The pointwise quadruple term `c_q V(2πmn/t) e^{itλ_q}`. -/
def quadPoint (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) : ℂ :=
  (quadCoeff N P h k : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
    Complex.exp ((t * quadFreq P h k : ℝ) * I)

/-- The contribution of the ratio `c` to the expansion. -/
def fiberTerm (ψ : ℝ → ℝ) (α β : ℝ) (N : ℕ) (T : ℝ) (c : ℕ × ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c}, quadTerm ψ α β N T P h k

theorem complex_support_subset {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) :
    Function.support (fun x : ℝ => (ψ x : ℂ)) ⊆ Icc 1 2 := by
  intro x hx; apply hsupp; intro h0; apply hx; simp [h0]

theorem quadTerm_eq_latticeSum {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ}
    (N : ℕ) {T : ℝ} (hT : 0 < T) (P : ℕ × ℕ) (h k : ℕ) :
    quadTerm ψ α β N T P h k =
      latticeSum (fun x => (ψ (x / T) : ℂ) * quadPoint N P h k (α * x + β)) 0 := by
  have hs := complex_support_subset hsupp
  unfold quadTerm
  rw [latticeSum_eq_sum (support_cutoff_subset hs hT _),
    latticeSum_eq_sum (support_cutoff_subset hs hT _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  unfold quadPoint
  rw [cexp_progression]
  simp only [mul_zero, unitExp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  ring

theorem norm_quadPoint (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) :
    ‖quadPoint N P h k t‖ = |quadCoeff N P h k| * ‖smoothAFECutoff (2 * Real.pi * pairProd P / t)‖ := by
  unfold quadPoint
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]

theorem summable_norm_quadPoint {t : ℝ} (ht : 0 < t) (N : ℕ) (h k : ℕ) :
    Summable (fun P : ℕ × ℕ => ‖quadPoint N P h k t‖) := by
  have hL : 0 < t / (2 * Real.pi) := by positivity
  refine ((ZetaNotch.summable_direct_envelope hL).mul_left |mollAmp N h * mollAmp N k|).congr
    fun P => ?_
  rw [norm_quadPoint, show 2 * Real.pi * pairProd P / t = pairProd P / (t / (2 * Real.pi)) by
    field_simp]
  unfold quadCoeff
  simp only [abs_mul, abs_of_pos (ZetaNotch.pairAmp_pos P)]
  ring

theorem summable_quadTerm {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ} (N : ℕ)
    {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) (h k : ℕ) :
    Summable (fun P : ℕ × ℕ => quadTerm ψ α β N T P h k) := by
  have hs := complex_support_subset hsupp
  simp_rw [quadTerm_eq_latticeSum hsupp N hT, latticeSum_eq_sum (support_cutoff_subset hs hT _)]
  refine summable_sum fun ℓ _ => ?_
  by_cases h0 : ψ ((ℓ : ℝ) / T) = 0
  · simp only [h0, Complex.ofReal_zero, zero_mul]; exact summable_zero
  · refine (Summable.of_norm (summable_norm_quadPoint (hpos ℓ h0) N h k)).mul_left _ |>.mul_right _

/-- **The fibre decomposition** `Σ_q X_q = Σ_c Φ_T(c)`. -/
theorem hasSum_fiberTerm {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ} (N : ℕ)
    {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) :
    HasSum (fiberTerm ψ α β N T) (∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      quadTerm ψ α β N T P h k) := by
  rw [Summable.tsum_finsetSum fun h _ => summable_sum fun k _ =>
      summable_quadTerm hsupp N hT hpos h k]
  unfold fiberTerm
  refine hasSum_sum fun h _ => ?_
  rw [Summable.tsum_finsetSum fun k _ => summable_quadTerm hsupp N hT hpos h k]
  refine hasSum_sum fun k _ => ?_
  exact (summable_quadTerm hsupp N hT hpos h k).hasSum.tsum_fiberwise (fun P => quadRatio P h k)

theorem tsum_fiber_quadTerm {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ}
    (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) (h k : ℕ)
    (c : ℕ × ℕ) :
    ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c}, quadTerm ψ α β N T P h k =
      latticeSum (fun x => (ψ (x / T) : ℂ) *
        ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c}, quadPoint N P h k (α * x + β)) 0 := by
  have hs := complex_support_subset hsupp
  simp_rw [quadTerm_eq_latticeSum hsupp N hT, latticeSum_eq_sum (support_cutoff_subset hs hT _)]
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [tsum_mul_right, tsum_mul_left]
  · intro ℓ _
    by_cases h0 : ψ ((ℓ : ℝ) / T) = 0
    · simp only [h0, Complex.ofReal_zero, zero_mul]; exact summable_zero
    · exact ((Summable.of_norm (summable_norm_quadPoint (hpos ℓ h0) N h k)).subtype _).mul_left _
        |>.mul_right _

theorem sum_fiber_quadPoint (N : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {t : ℝ} (ht : 0 < t) :
    ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = (a, b)}, quadPoint N P h k t =
      ((Real.sqrt ((a : ℝ) * b))⁻¹ : ℂ) * Complex.exp ((t * (Real.log a - Real.log b) : ℝ) * I) *
        ratioForm N a b t := by
  unfold ratioForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact tsum_fiber_quadPoint N (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1 hab ha hb ht

/-- **The fibre term of a coprime ratio** `a/b` is
`Σ_ℓ ψ(ℓ/T) (ab)^{−1/2} e^{it_ℓ log(a/b)} F(a, b, t_ℓ)`. -/
theorem fiberTerm_eq {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ} (N : ℕ)
    {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    fiberTerm ψ α β N T (a, b) = latticeSum (fun x => (ψ (x / T) : ℂ) *
      (((Real.sqrt ((a : ℝ) * b))⁻¹ : ℂ) *
        Complex.exp (((α * x + β) * (Real.log a - Real.log b) : ℝ) * I) *
          ratioForm N a b (α * x + β))) 0 := by
  have hs := complex_support_subset hsupp
  unfold fiberTerm
  simp_rw [tsum_fiber_quadTerm hsupp N hT hpos]
  rw [latticeSum_eq_sum (support_cutoff_subset hs hT _)]
  simp_rw [latticeSum_eq_sum (support_cutoff_subset hs hT _)]
  have key : ∀ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, (ψ ((ℓ : ℝ) / T) : ℂ) *
      (((Real.sqrt ((a : ℝ) * b))⁻¹ : ℂ) *
        Complex.exp (((α * ℓ + β) * (Real.log a - Real.log b) : ℝ) * I) *
          ratioForm N a b (α * ℓ + β)) * unitExp (ℓ * 0) =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, (ψ ((ℓ : ℝ) / T) : ℂ) *
        (∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = (a, b)}, quadPoint N P h k (α * ℓ + β)) *
          unitExp (ℓ * 0) := by
    intro ℓ _
    by_cases h0 : ψ ((ℓ : ℝ) / T) = 0
    · simp [h0]
    · rw [← sum_fiber_quadPoint N hab ha hb (hpos ℓ h0), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl key, Finset.sum_comm (s := Finset.Icc ⌈T⌉ ⌊2 * T⌋)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm (s := Finset.Icc ⌈T⌉ ⌊2 * T⌋)]

/-- Ratios of quadruples are coprime pairs of positive integers. -/
theorem quadRatio_spec (P : ℕ × ℕ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Nat.Coprime (quadRatio P h k).1 (quadRatio P h k).2 ∧ 0 < (quadRatio P h k).1 ∧
      0 < (quadRatio P h k).2 := by
  have hx : 0 < (P.2 + 1) * k := Nat.mul_pos (Nat.succ_pos _) hk
  have hy : 0 < (P.1 + 1) * h := Nat.mul_pos (Nat.succ_pos _) hh
  have hg : 0 < Nat.gcd ((P.2 + 1) * k) ((P.1 + 1) * h) := Nat.gcd_pos_of_pos_left _ hx
  exact ⟨Nat.coprime_div_gcd_div_gcd hg, Nat.div_pos (Nat.gcd_le_left _ hx) hg,
    Nat.div_pos (Nat.gcd_le_right _ hy) hg⟩

/-- Ratios that are not coprime pairs of positive integers have empty fibres. -/
theorem fiberTerm_eq_zero {ψ : ℝ → ℝ} {α β : ℝ} {N : ℕ} {T : ℝ} {c : ℕ × ℕ}
    (hc : ¬ (Nat.Coprime c.1 c.2 ∧ 0 < c.1 ∧ 0 < c.2)) : fiberTerm ψ α β N T c = 0 := by
  unfold fiberTerm
  refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun k hk => ?_
  have hempty : {P : ℕ × ℕ | quadRatio P h k = c} = ∅ := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hP
    exact hc (hP ▸ quadRatio_spec P (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1)
  rw [hempty]
  exact tsum_empty

end

end RHTower.VerticalAP
