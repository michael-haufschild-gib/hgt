import GaloisForLFunctions.HTGeometry.RamificationGNSFusion

/-!
# Spectral fusion and marked reconstruction of a ramification power formation

Continuing the GNS splitting `ℓ²(A_{rm}) = T_r ℓ²(A_m) ⊕ ℓ²(X_{m,r})`:

* `⟨Ω_{rm,σ}, Q Ω_{rm,σ}⟩ = β_{m,r}(σ)`;
* for logarithmic clocks on their maximal domains, `D_{rm} T_r = r T_r D_m` and
  `D_{rm} ≅ r D_m ⊕ D^{ex}` (a vector is in the domain of `D_{rm}` exactly when both coordinate
  parts are, and then `D_{rm} w = T_r(r D_m w_{in}) + J(D^{ex} w_{ex})`);
* `S_{rm}(z) = S_m(rz) + C_{m,r}(z)` for `Re z > 1` and the characteristic fusion;
* a diagonal operator with summable nonnegative weights is positive and trace class with trace
  the sum of the weights, whence `Tr e^{-tD_{rm}} = Tr e^{-rtD_m} + Tr e^{-tD^{ex}}`;
* the scalar spectral measure `Σ_n |Ω(n)|² δ_{log n}` of `Ω_{rm,σ}` is `P_{rm,σ}`; those of the
  range and defect parts are `α I` and `β Q`; multiplying by the marked mass gives `μ_{rm,σ}`;
  normalization forgets the scale: `c μ` and `μ` have the same law.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationExcess

open _root_.RHTower LpDiagonal

variable {m r : ℕ}

/-! ### The defect expectation -/

theorem norm_sq_restrInr_shellVector (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    ‖restrInr (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ)‖ ^ 2 =
      excessFraction m r σ := by
  rw [lp_two_norm_sq_eq_tsum]
  simp_rw [restrInr_apply, shellSplit_symm_inr]
  simp_rw [norm_sq_eulerShellSource_v]
  rw [tsum_div_const, excessFraction, excessSum]

/-- **`(FE.24)`**: `⟨Ω_{rm,σ}, Q_r Ω_{rm,σ}⟩ = β_{m,r}(σ)`. -/
theorem inner_defectProj_shellVector (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    ⟪shellVector (one_le_mul_m hm hr) hσ,
      defectProj (shellSplit (by omega)) (shellVector (one_le_mul_m hm hr) hσ)⟫_ℂ =
      (excessFraction m r σ : ℂ) := by
  rw [defectProj_apply, ← inner_conj_symm, inner_splitInr]
  have hb : ⟪restrInr (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ),
      restrInr (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ)⟫_ℂ =
      ((excessFraction m r σ : ℝ) : ℂ) := by
    rw [← norm_sq_restrInr_shellVector hm hr hσ, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hb, Complex.conj_ofReal]

/-- `⟨Ω_{rm,σ}, (1 - Q_r) Ω_{rm,σ}⟩ = α_{m,r}(σ)`. -/
theorem inner_rangeProj_shellVector (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    ⟪shellVector (one_le_mul_m hm hr) hσ,
      rangeProj (shellSplit (by omega)) (shellVector (one_le_mul_m hm hr) hσ)⟫_ℂ =
      (survival m r σ : ℂ) := by
  have h0 : defectProj (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ) =
      shellVector (one_le_mul_m hm hr) hσ -
        rangeProj (shellSplit (by omega)) (shellVector (one_le_mul_m hm hr) hσ) := rfl
  have h1 : rangeProj (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ) =
      shellVector (one_le_mul_m hm hr) hσ -
        defectProj (shellSplit (by omega)) (shellVector (one_le_mul_m hm hr) hσ) := by
    rw [h0, sub_sub_cancel]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (survival_add_excessFraction hm hr hσ)
  push_cast at h
  rw [h1, inner_sub_right, inner_defectProj_shellVector hm hr hσ, inner_self_eq_norm_sq_to_K,
    norm_eulerShellSource_v]
  push_cast
  linear_combination -h

/-! ### Logarithmic clocks on maximal domains -/

section Clock

variable {α : Type*}

/-- The maximal domain of the diagonal operator with real symbol `lam`. -/
def clockDomain (lam : α → ℝ) : Set (LpTwo α) :=
  {v | Summable fun i => ‖(lam i : ℂ) * (v : α → ℂ) i‖ ^ 2}

/-- The diagonal operator `(D v)_i = lam_i v_i` on its maximal domain. -/
def clockMap (lam : α → ℝ) (v : LpTwo α) (hv : v ∈ clockDomain lam) : LpTwo α :=
  ⟨fun i => (lam i : ℂ) * (v : α → ℂ) i, memℓp_two_of_summable hv⟩

@[simp] theorem clockMap_apply (lam : α → ℝ) (v : LpTwo α) (hv : v ∈ clockDomain lam) (i : α) :
    (clockMap lam v hv : α → ℂ) i = (lam i : ℂ) * (v : α → ℂ) i := rfl

variable {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) {lamκ : κ → ℝ} {lamι : ι → ℝ} {lamξ : ξ → ℝ} {c : ℝ}

theorem mem_clockDomain_iff (hc : c ≠ 0) (hι : ∀ i, lamκ (e.symm (Sum.inl i)) = c * lamι i)
    (hξ : ∀ x, lamκ (e.symm (Sum.inr x)) = lamξ x) (w : LpTwo κ) :
    w ∈ clockDomain lamκ ↔
      restrInl e w ∈ clockDomain lamι ∧ restrInr e w ∈ clockDomain lamξ := by
  have hgι : ∀ i, ‖(lamκ (e.symm (Sum.inl i)) : ℂ) * (w : κ → ℂ) (e.symm (Sum.inl i))‖ ^ 2 =
      ‖(c : ℂ)‖ ^ 2 * ‖(lamι i : ℂ) * (restrInl e w : ι → ℂ) i‖ ^ 2 := fun i => by
    simp only [hι, restrInl_apply, Complex.ofReal_mul, norm_mul]
    ring
  have hgξ : ∀ x, ‖(lamκ (e.symm (Sum.inr x)) : ℂ) * (w : κ → ℂ) (e.symm (Sum.inr x))‖ ^ 2 =
      ‖(lamξ x : ℂ) * (restrInr e w : ξ → ℂ) x‖ ^ 2 :=
    fun x => by simp only [hξ, restrInr_apply]
  have hc' : 0 < ‖(c : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.2 (by exact_mod_cast hc)) 2
  constructor
  · intro hw
    have h := (e.symm.summable_iff.2 hw)
    refine ⟨?_, ?_⟩
    · have h1 := (h.comp_injective Sum.inl_injective).div_const (‖(c : ℂ)‖ ^ 2)
      refine h1.congr fun i => ?_
      simp only [Function.comp_apply]
      rw [hgι, mul_div_cancel_left₀ _ hc'.ne']
    · exact (h.comp_injective Sum.inr_injective).congr fun x => by
        simp only [Function.comp_apply]
        rw [hgξ]
  · rintro ⟨h1, h2⟩
    have h : Summable ((fun k => ‖(lamκ k : ℂ) * (w : κ → ℂ) k‖ ^ 2) ∘ e.symm) := by
      refine Summable.sum _ ?_ ?_
      · exact (h1.mul_left (‖(c : ℂ)‖ ^ 2)).congr fun i => by
          simp only [Function.comp_apply]
          rw [hgι]
      · exact h2.congr fun x => by
          simp only [Function.comp_apply]
          rw [hgξ]
    exact e.symm.summable_iff.1 h

/-- **`D_κ ≅ c D_ι ⊕ D_ξ`** along the splitting: on the maximal domain,
`D_κ w = T (c D_ι w_ι) + J (D_ξ w_ξ)`. -/
theorem clockMap_split (hc : c ≠ 0) (hι : ∀ i, lamκ (e.symm (Sum.inl i)) = c * lamι i)
    (hξ : ∀ x, lamκ (e.symm (Sum.inr x)) = lamξ x) (w : LpTwo κ) (hw : w ∈ clockDomain lamκ) :
    clockMap lamκ w hw =
      splitInl e ((c : ℂ) • clockMap lamι (restrInl e w)
          ((mem_clockDomain_iff e hc hι hξ w).1 hw).1) +
        splitInr e (clockMap lamξ (restrInr e w) ((mem_clockDomain_iff e hc hι hξ w).1 hw).2) := by
  refine lp.ext (funext fun k => ?_)
  simp only [clockMap_apply, lp.coeFn_add, Pi.add_apply, splitInl_apply, splitInr_apply,
    extendSum_apply]
  rcases h : e k with i | x
  · have hk : k = e.symm (Sum.inl i) := by rw [← h, Equiv.symm_apply_apply]
    simp only [Sum.elim_inl, lp.coeFn_zero, Pi.zero_apply, add_zero, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, clockMap_apply, restrInl_apply]
    rw [hk, hι, Complex.ofReal_mul]
    ring
  · have hk : k = e.symm (Sum.inr x) := by rw [← h, Equiv.symm_apply_apply]
    simp only [Sum.elim_inr, lp.coeFn_zero, Pi.zero_apply, zero_add, clockMap_apply,
      restrInr_apply]
    rw [hk, hξ]

/-- The intertwining `D_κ T = c T D_ι` on maximal domains. -/
theorem splitInl_mem_clockDomain_iff (hc : c ≠ 0)
    (hι : ∀ i, lamκ (e.symm (Sum.inl i)) = c * lamι i)
    (hξ : ∀ x, lamκ (e.symm (Sum.inr x)) = lamξ x) (a : LpTwo ι) :
    splitInl e a ∈ clockDomain lamκ ↔ a ∈ clockDomain lamι := by
  rw [mem_clockDomain_iff e hc hι hξ, splitInl_apply, restrInl_extendSum, restrInr_extendSum]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  show Summable fun x => ‖(lamξ x : ℂ) * ((0 : LpTwo ξ) : ξ → ℂ) x‖ ^ 2
  simp

theorem clockMap_splitInl (hc : c ≠ 0) (hι : ∀ i, lamκ (e.symm (Sum.inl i)) = c * lamι i)
    (hξ : ∀ x, lamκ (e.symm (Sum.inr x)) = lamξ x) (a : LpTwo ι) (ha : a ∈ clockDomain lamι) :
    clockMap lamκ (splitInl e a) ((splitInl_mem_clockDomain_iff e hc hι hξ a).2 ha) =
      (c : ℂ) • splitInl e (clockMap lamι a ha) := by
  refine lp.ext (funext fun k => ?_)
  simp only [clockMap_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, splitInl_apply,
    extendSum_apply]
  rcases h : e k with i | x
  · have hk : k = e.symm (Sum.inl i) := by rw [← h, Equiv.symm_apply_apply]
    simp only [Sum.elim_inl, clockMap_apply]
    rw [hk, hι, Complex.ofReal_mul]
    ring
  · simp

end Clock

/-- The logarithmic clock symbol on `A_m`. -/
def shellLog (m : ℕ) (n : EulerShell m) : ℝ := Real.log (n : ℕ)

/-- The logarithmic clock symbol on `X_{m,r}`. -/
def excessLog (m r : ℕ) (N : ExcessShell m r) : ℝ := Real.log (N : ℕ)

theorem shellLog_inl (hr : r ≠ 0) (k : EulerShell m) :
    shellLog (r * m) ((shellSplit hr).symm (Sum.inl k)) = r * shellLog m k := by
  rw [shellSplit_symm_inl, shellLog, shellLog, shellPow_val, Nat.cast_pow, Real.log_pow]

theorem shellLog_inr (hr : r ≠ 0) (N : ExcessShell m r) :
    shellLog (r * m) ((shellSplit hr).symm (Sum.inr N)) = excessLog m r N := rfl

/-- **`(FE.23)`, the intertwining**: `T_r` maps the maximal domain of `D_m` exactly onto vectors of
the domain of `D_{rm}` in its range, and `D_{rm} T_r = r T_r D_m`. -/
theorem shellClock_intertwining (hr : r ≠ 0) (a : LpTwo (EulerShell m)) :
    (powIsometry hr a ∈ clockDomain (shellLog (r * m)) ↔ a ∈ clockDomain (shellLog m)) ∧
      ∀ ha : a ∈ clockDomain (shellLog m),
        ∃ h, clockMap (shellLog (r * m)) (powIsometry hr a) h =
          (r : ℂ) • powIsometry hr (clockMap (shellLog m) a ha) := by
  have hc : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  refine ⟨splitInl_mem_clockDomain_iff (shellSplit hr) hc (shellLog_inl hr) (shellLog_inr hr) a,
    fun ha => ⟨(splitInl_mem_clockDomain_iff (shellSplit hr) hc (shellLog_inl hr)
      (shellLog_inr hr) a).2 ha, ?_⟩⟩
  have := clockMap_splitInl (shellSplit hr) hc (shellLog_inl hr) (shellLog_inr hr) a ha
  simpa using this

/-- **`(FE.23)`, the splitting**: `D_{rm} ≅ r D_m ⊕ D^{ex}` on maximal domains. -/
theorem shellClock_split (hr : r ≠ 0) (w : LpTwo (EulerShell (r * m))) :
    (w ∈ clockDomain (shellLog (r * m)) ↔
      restrInl (shellSplit hr) w ∈ clockDomain (shellLog m) ∧
        restrInr (shellSplit hr) w ∈ clockDomain (excessLog m r)) ∧
      ∀ hw : w ∈ clockDomain (shellLog (r * m)), ∃ h₁ h₂,
        clockMap (shellLog (r * m)) w hw =
          powIsometry hr ((r : ℂ) • clockMap (shellLog m) (restrInl (shellSplit hr) w) h₁) +
            excessIsometry hr (clockMap (excessLog m r) (restrInr (shellSplit hr) w) h₂) := by
  have hc : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  refine ⟨mem_clockDomain_iff (shellSplit hr) hc (shellLog_inl hr) (shellLog_inr hr) w,
    fun hw => ⟨((mem_clockDomain_iff (shellSplit hr) hc (shellLog_inl hr) (shellLog_inr hr) w).1
      hw).1, ((mem_clockDomain_iff (shellSplit hr) hc (shellLog_inl hr) (shellLog_inr hr) w).1
      hw).2, ?_⟩⟩
  have := clockMap_split (shellSplit hr) hc (shellLog_inl hr) (shellLog_inr hr) w hw
  simpa using this

/-! ### Complex Dirichlet split and characteristic fusion -/

/-- The complex excess series `C_{m,r}(z) = Σ_{N ∈ X_{m,r}} N^{-z}`. -/
def excessSeries (m r : ℕ) (z : ℂ) : ℂ := ∑' N : ExcessShell m r, ((N : ℕ) : ℂ) ^ (-z)

theorem excessSeries_ofReal (m r : ℕ) (σ : ℝ) : excessSeries m r σ = (excessSum m r σ : ℂ) := by
  rw [excessSeries, excessSum, Complex.ofReal_tsum]
  refine tsum_congr fun N => ?_
  have hN : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_neg, Complex.ofReal_cpow hN, Complex.ofReal_natCast]

theorem summable_cpow_shell {α : Type*} {f : α → ℕ} (hf : Function.Injective f)
    (hf2 : ∀ a, 1 ≤ f a) {z : ℂ} (hz : 1 < z.re) :
    Summable fun a => ((f a : ℕ) : ℂ) ^ (-z) := by
  refine Summable.of_norm ?_
  have h := (Real.summable_nat_rpow.2 (show -z.re < -1 by linarith)).comp_injective hf
  refine h.congr fun a => ?_
  rw [Function.comp_apply, Complex.norm_natCast_cpow_of_pos (by have := hf2 a; omega),
    Complex.neg_re]

theorem natCast_pow_cpow (k r : ℕ) (hk : k ≠ 0) (z : ℂ) :
    (((k ^ r : ℕ) : ℕ) : ℂ) ^ (-z) = ((k : ℕ) : ℂ) ^ (-((r : ℂ) * z)) := by
  have hk' : ((k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hk
  have hkr : (((k ^ r : ℕ) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero r hk
  rw [Complex.cpow_def_of_ne_zero hkr, Complex.cpow_def_of_ne_zero hk', ← Complex.natCast_log,
    ← Complex.natCast_log, Nat.cast_pow, Real.log_pow]
  congr 1
  push_cast
  ring

/-- **`(FE.7)`**: `S_{rm}(z) = S_m(rz) + C_{m,r}(z)` for `Re z > 1`. -/
theorem eulerShellSeries_split (hr : r ≠ 0) {z : ℂ} (hz : 1 < z.re) :
    eulerShellSeries (r * m) z = eulerShellSeries m ((r : ℂ) * z) + excessSeries m r z := by
  have hrz : 1 < ((r : ℂ) * z).re := by
    have h1 : ((r : ℂ) * z).re = (r : ℝ) * z.re := by simp [Complex.mul_re]
    have : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
    rw [h1]
    nlinarith
  rw [eulerShellSeries, ← (shellSplit hr).symm.tsum_eq]
  rw [Summable.tsum_sum]
  · simp only [shellSplit_symm_inl, shellSplit_symm_inr, shellPow_val]
    congr 1
    exact tsum_congr fun k => natCast_pow_cpow _ _ (by have := k.2.1; omega) z
  · refine (summable_cpow_shell (f := fun k : EulerShell m => (k : ℕ)) Subtype.val_injective
      (fun k => by have := k.2.1; omega) hrz).congr fun k => ?_
    exact (natCast_pow_cpow _ _ (by have := k.2.1; omega) z).symm
  · exact summable_cpow_shell (f := fun N : ExcessShell m r => ((N : EulerShell (r * m)) : ℕ))
      (Subtype.val_injective.comp Subtype.val_injective) (fun N => by have := N.1.2.1; omega) hz

/-- **Corollary 3.2, `(FE.25)` (characteristic fusion)**: for every real `t`,
`S_{rm}(σ+it)/S_{rm}(σ) = α S_m(r(σ+it))/S_m(rσ) + β C(σ+it)/C(σ)`. -/
theorem characteristic_fusion (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    eulerShellSeries (r * m) (σ + t * Complex.I) / (eulerShellSum (r * m) σ : ℂ) =
      (survival m r σ : ℂ) * (eulerShellSeries m ((r : ℂ) * (σ + t * Complex.I)) /
          (eulerShellSum m (r * σ) : ℂ)) +
        (excessFraction m r σ : ℂ) * (excessSeries m r (σ + t * Complex.I) /
          (excessSum m r σ : ℂ)) := by
  have hS := eulerShellSum_pos (one_le_mul_m hm hr) hσ
  have hSm := eulerShellSum_pos hm (one_lt_mul_of_two_le hr hσ)
  have hC := excessSum_pos (m := m) (by omega) hr hσ
  have hS' : (eulerShellSum (r * m) σ : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hSm' : (eulerShellSum m (r * σ) : ℂ) ≠ 0 := by exact_mod_cast hSm.ne'
  have hC' : (excessSum m r σ : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [eulerShellSeries_split (by omega) (by simpa using hσ), survival, excessFraction]
  push_cast
  field_simp

/-- The GNS form of the characteristic fusion:
`⟨Ω_{m,σ}, e^{-itD_m} Ω_{m,σ}⟩ = S_m(σ+it)/S_m(σ)`. -/
theorem gns_characteristic (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ⟪shellVector hm hσ, shellPhase (t * Complex.I) (by simp) (shellVector hm hσ)⟫_ℂ =
      eulerShellSeries m (σ + t * Complex.I) / (eulerShellSum m σ : ℂ) :=
  inner_v_shellPhase hm hσ _ _

/-! ### Heat traces -/

section Trace

variable {α : Type*} [DecidableEq α]

/-- A diagonal operator with summable nonnegative weights is the right Gram of the frame
`√w_i e_i`: it is positive, trace class, and its trace is `Σ w_i`. -/
theorem diag_traceClass {w : α → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hs : Summable w) :
    (lpDiag (fun i => (w i : ℂ)) 1 zero_le_one fun i => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hw0 i)]; exact hw1 i).IsPositive ∧
      MemSchattenClass 1 (lpDiag (fun i => (w i : ℂ)) 1 zero_le_one fun i => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hw0 i)]; exact hw1 i) ∧
      (lpDiag (fun i => (w i : ℂ)) 1 zero_le_one fun i => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hw0 i)]; exact hw1 i).opTrace =
        ((∑' i, w i : ℝ) : ℂ) := by
  set v : α → LpTwo α := fun i => ((Real.sqrt (w i) : ℝ) : ℂ) • lp.single 2 i 1
  have hv : Summable fun i => ‖v i‖ ^ 2 := hs.congr fun i => by
    simp only [v, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_one, mul_one, Real.sq_sqrt (hw0 i)]
  have hG := rightGram_traceClass hv
  have heq : ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) ∘L
      squareSummableSynthesis v hv = lpDiag (fun i => (w i : ℂ)) 1 zero_le_one fun i => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hw0 i)]; exact hw1 i := by
    refine ext_of_inner_single fun i j => ?_
    rw [inner_single_rightGram_single, lp.inner_single_left, RCLike.inner_apply]
    simp only [v, lpDiag_coe, lp.single_apply, map_one, mul_one]
    rw [inner_smul_left, inner_smul_right, lp.inner_single_left, lp.single_apply,
      RCLike.inner_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Pi.single_eq_same, map_one, mul_one, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw0 i)]
    · rw [Pi.single_eq_of_ne hij]
      simp
  rw [← heq]
  refine ⟨hG.1, hG.2.1, hG.2.2.trans ?_⟩
  congr 2
  funext i
  simp only [v, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_one, mul_one, Real.sq_sqrt (hw0 i)]

end Trace

theorem rpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) : (n : ℝ) ^ (-t) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-- The heat operator `e^{-tD}` of a logarithmic clock on a set of integers `≥ 1`. -/
def heatOp {α : Type*} (f : α → ℕ) (hf : ∀ a, 1 ≤ f a) {t : ℝ} (ht : 0 ≤ t) :
    LpTwo α →L[ℂ] LpTwo α :=
  lpDiag (fun a => ((((f a : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ)) 1 zero_le_one fun a => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact rpow_neg_le_one (hf a) ht

/-- The heat weights are the exponentials of the logarithmic clock: `n^{-t} = e^{-t log n}`. -/
theorem rpow_neg_eq_exp_neg_log {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℝ) ^ (-t) = Real.exp (-t * Real.log n) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega)), mul_comm]

theorem heatOp_traceClass {α : Type*} [DecidableEq α] {f : α → ℕ} (hfi : Function.Injective f)
    (hf : ∀ a, 1 ≤ f a) {t : ℝ} (ht : 1 < t) :
    (heatOp f hf (zero_le_one.trans ht.le)).IsPositive ∧
      MemSchattenClass 1 (heatOp f hf (zero_le_one.trans ht.le)) ∧
      (heatOp f hf (zero_le_one.trans ht.le)).opTrace = ((∑' a, ((f a : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ) :=
  diag_traceClass (fun _ => by positivity) (fun a => rpow_neg_le_one (hf a) (by linarith))
    ((Real.summable_nat_rpow.2 (by linarith)).comp_injective hfi)

/-- **Corollary 3.3, `(FE.26)` (heat-trace valuation)**: for `t > 1` the three heat operators are
positive and trace class, with `Tr e^{-tD_{rm}} = Tr e^{-rtD_m} + Tr e^{-tD^{ex}}`, the traces being
`S_{rm}(t)`, `S_m(rt)` and `C_{m,r}(t)`. -/
theorem heatTrace_fusion (hr : 2 ≤ r) {t : ℝ} (ht : 1 < t) :
    (heatOp (fun n : EulerShell (r * m) => (n : ℕ)) (fun n => by have := n.2.1; omega)
        (zero_le_one.trans ht.le)).opTrace = (eulerShellSum (r * m) t : ℂ) ∧
      (heatOp (fun n : EulerShell m => (n : ℕ)) (fun n => by have := n.2.1; omega)
        (zero_le_one.trans (one_lt_mul_of_two_le hr ht).le)).opTrace =
        (eulerShellSum m (r * t) : ℂ) ∧
      (heatOp (fun N : ExcessShell m r => ((N : EulerShell (r * m)) : ℕ))
        (fun N => by have := N.1.2.1; omega) (zero_le_one.trans ht.le)).opTrace =
        (excessSum m r t : ℂ) ∧
      (eulerShellSum (r * m) t : ℂ) = eulerShellSum m (r * t) + excessSum m r t := by
  classical
  refine ⟨(heatOp_traceClass Subtype.val_injective _ ht).2.2, ?_, ?_, ?_⟩
  · exact (heatOp_traceClass Subtype.val_injective _ (one_lt_mul_of_two_le hr ht)).2.2
  · exact (heatOp_traceClass (Subtype.val_injective.comp Subtype.val_injective) _ ht).2.2
  · exact_mod_cast eulerShellSum_split (by omega) ht

/-! ### Marked spectral reconstruction -/

/-- The scalar spectral measure `Σ_i |v_i|² δ_{lam_i}` of a diagonal clock in a vector `v`. -/
def spectralMeasure {α : Type*} (lam : α → ℝ) (v : LpTwo α) : Measure ℝ :=
  atomic (fun i => ‖(v : α → ℂ) i‖ ^ 2) lam

theorem smul_atomic {ι : Type*} {c : ℝ} (hc : 0 ≤ c) (w x : ι → ℝ) (_hw : ∀ i, 0 ≤ w i) :
    ENNReal.ofReal c • atomic w x = atomic (fun i => c * w i) x := by
  ext s hs
  rw [Measure.smul_apply, atomic_apply _ _ hs, atomic_apply _ _ hs, smul_eq_mul,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [ENNReal.ofReal_mul hc, mul_assoc]

theorem atomic_congr {ι : Type*} {w w' : ι → ℝ} (h : ∀ i, w i = w' i) (x : ι → ℝ) :
    atomic w x = atomic w' x := by
  rw [funext h]

/-- Atoms of zero weight do not contribute. -/
theorem atomic_split_zero {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) (w : ι → ℝ) (x : κ → ℝ) :
    atomic (fun k => Sum.elim w 0 (e k)) x = atomic w (fun i => x (e.symm (Sum.inl i))) := by
  rw [← atomic_comp_equiv e.symm, atomic_sum]
  have h0 : atomic (((fun k => Sum.elim w 0 (e k)) ∘ e.symm) ∘ Sum.inr)
      ((x ∘ e.symm) ∘ Sum.inr) = 0 := by
    ext s hs
    rw [atomic_apply _ _ hs]
    simp
  rw [h0, add_zero]
  congr 1
  funext i
  simp

theorem atomic_split_zero_right {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) (w : ξ → ℝ) (x : κ → ℝ) :
    atomic (fun k => Sum.elim 0 w (e k)) x = atomic w (fun y => x (e.symm (Sum.inr y))) := by
  rw [← atomic_comp_equiv e.symm, atomic_sum]
  have h0 : atomic (((fun k => Sum.elim 0 w (e k)) ∘ e.symm) ∘ Sum.inl)
      ((x ∘ e.symm) ∘ Sum.inl) = 0 := by
    ext s hs
    rw [atomic_apply _ _ hs]
    simp
  rw [h0, zero_add]
  congr 1
  funext y
  simp

/-- The spectral measure of a vector in the range of `T` is carried by the `ι`-atoms. -/
theorem spectralMeasure_splitInl {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) (lam : κ → ℝ) (a : LpTwo ι) :
    spectralMeasure lam (splitInl e a) =
      atomic (fun i => ‖(a : ι → ℂ) i‖ ^ 2) (fun i => lam (e.symm (Sum.inl i))) := by
  have h : ∀ k, ‖((splitInl e a : LpTwo κ) : κ → ℂ) k‖ ^ 2 =
      Sum.elim (fun i => ‖(a : ι → ℂ) i‖ ^ 2) (0 : ξ → ℝ) (e k) := fun k => by
    simp only [splitInl_apply, extendSum_apply]
    rcases hk : e k with i | x <;> simp
  rw [spectralMeasure, atomic_congr h, atomic_split_zero]

/-- The spectral measure of a vector in the range of `J` is carried by the `ξ`-atoms. -/
theorem spectralMeasure_splitInr {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) (lam : κ → ℝ) (b : LpTwo ξ) :
    spectralMeasure lam (splitInr e b) =
      atomic (fun x => ‖(b : ξ → ℂ) x‖ ^ 2) (fun x => lam (e.symm (Sum.inr x))) := by
  have h : ∀ k, ‖((splitInr e b : LpTwo κ) : κ → ℂ) k‖ ^ 2 =
      Sum.elim (0 : ι → ℝ) (fun x => ‖(b : ξ → ℂ) x‖ ^ 2) (e k) := fun k => by
    simp only [splitInr_apply, extendSum_apply]
    rcases hk : e k with i | x <;> simp
  rw [spectralMeasure, atomic_congr h, atomic_split_zero_right]

/-- **Theorem 4.1 (1)**: the scalar spectral measure of the clock in the cyclic vector is the
formation law, `Σ_n |Ω_{m,σ}(n)|² δ_{log n} = P_{m,σ}`. -/
theorem spectralMeasure_shellVector (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ) :
    spectralMeasure (shellLog m) (shellVector hm hσ) = shellLaw m σ := by
  have hS := eulerShellSum_pos hm hσ
  rw [spectralMeasure, shellLaw, shellMeasure, smul_atomic (inv_nonneg.2 hS.le) _ _
    (fun _ => by positivity)]
  refine atomic_congr (fun n => ?_) _
  rw [norm_sq_eulerShellSource_v, div_eq_inv_mul]

/-- The spectral mass of an atom `{log n}` is the law's mass `P(n)`: the clock eigenvalues are
simple. -/
theorem atomic_singleton {ι : Type*} {w : ι → ℝ} {x : ι → ℝ} (hx : Function.Injective x)
    (i : ι) : atomic w x {x i} = ENNReal.ofReal (w i) := by
  rw [atomic_apply _ _ (measurableSet_singleton _), tsum_eq_single i fun j hj => by
    rw [indicator_of_notMem (by simpa using hx.ne hj), mul_zero]]
  simp

theorem shellLog_injective (m : ℕ) : Function.Injective (shellLog m) := fun a b h => by
  have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast (show 0 < (a : ℕ) by have := a.2.1; omega)
  have hb : (0 : ℝ) < (b : ℕ) := by exact_mod_cast (show 0 < (b : ℕ) by have := b.2.1; omega)
  exact Subtype.ext (by exact_mod_cast Real.log_injOn_pos ha hb h)

section Reconstruction

variable (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
include hm hr hσ

theorem restrInl_shellVector :
    restrInl (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ) =
      ((Real.sqrt (survival m r σ) : ℝ) : ℂ) • shellVector hm (one_lt_mul_of_two_le hr hσ) := by
  conv_lhs => rw [shellVector_fusion hm hr hσ]
  refine lp.ext (funext fun k => ?_)
  simp only [restrInl_apply, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    splitInl_apply, splitInr_apply, extendSum_apply, Equiv.apply_symm_apply, Sum.elim_inl,
    lp.coeFn_zero, Pi.zero_apply, smul_zero, add_zero]

theorem restrInr_shellVector :
    restrInr (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ) =
      ((Real.sqrt (excessFraction m r σ) : ℝ) : ℂ) • excessVector m r σ hσ := by
  conv_lhs => rw [shellVector_fusion hm hr hσ]
  refine lp.ext (funext fun x => ?_)
  simp only [restrInr_apply, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    splitInl_apply, splitInr_apply, extendSum_apply, Equiv.apply_symm_apply, Sum.elim_inr,
    lp.coeFn_zero, Pi.zero_apply, smul_zero, zero_add]

theorem rangeProj_shellVector :
    rangeProj (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ) =
      powIsometry (by omega)
        (restrInl (shellSplit (by omega)) (shellVector (one_le_mul_m hm hr) hσ)) := by
  rw [rangeProj, ContinuousLinearMap.comp_apply, adjoint_splitInl]
  rfl

/-- **Theorem 4.1 (4), inherited conditional**: the spectral measure of the range part
`(1 - Q_r) Ω_{rm,σ}` is `α I_{m,r,σ}`. -/
theorem spectralMeasure_rangeProj :
    spectralMeasure (shellLog (r * m))
        (rangeProj (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ)) =
      ENNReal.ofReal (survival m r σ) • inheritedLaw m r σ := by
  have hα := survival_pos hm hr hσ
  have hrσ := one_lt_mul_of_two_le hr hσ
  have hSm := eulerShellSum_pos hm hrσ
  rw [rangeProj_shellVector hm hr hσ, spectralMeasure_splitInl, restrInl_shellVector hm hr hσ,
    inheritedLaw, shellLaw, Measure.map_smul, shellMeasure, atomic_map _ _ (measurable_dilate r),
    smul_atomic (inv_nonneg.2 hSm.le) _ _ (fun _ => by positivity), smul_atomic hα.le _ _
    (fun _ => by positivity)]
  congr 1
  · funext k
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hα.le, norm_sq_eulerShellSource_v]
    ring
  · funext k
    simp only [Function.comp_apply, dilate]
    rw [shellLog_inl]
    rfl

/-- **Theorem 4.1 (2), (4), excess conditional**: the spectral measure of the defect part
`Q_r Ω_{rm,σ}` is `β Q_{m,r,σ}`, carried by the excess atoms. -/
theorem spectralMeasure_defectProj :
    spectralMeasure (shellLog (r * m))
        (defectProj (shellSplit (by omega : r ≠ 0)) (shellVector (one_le_mul_m hm hr) hσ)) =
      ENNReal.ofReal (excessFraction m r σ) • excessLaw m r σ := by
  have hβ := excessFraction_pos hm hr hσ
  have hC := excessSum_pos (m := m) (by omega) hr hσ
  rw [defectProj_apply, spectralMeasure_splitInr, restrInr_shellVector hm hr hσ, excessLaw,
    excessMeasure, smul_atomic (inv_nonneg.2 hC.le) _ _ (fun _ => by positivity),
    smul_atomic hβ.le _ _ (fun _ => by positivity)]
  congr 1
  · funext N
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hβ.le,
      norm_sq_excessVector_apply (by omega) hr hσ]
    ring

/-- **Theorem 4.1 (5)**: the marked total mass restores the unnormalized formation measure. -/
theorem shellMeasure_eq_mass_smul_spectral :
    ENNReal.ofReal (eulerShellSum (r * m) σ) •
        spectralMeasure (shellLog (r * m)) (shellVector (one_le_mul_m hm hr) hσ) =
      shellMeasure (r * m) σ := by
  have hS := eulerShellSum_pos (one_le_mul_m hm hr) hσ
  rw [spectralMeasure_shellVector, shellLaw, smul_smul, ← ENNReal.ofReal_mul hS.le,
    mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one, one_smul]

end Reconstruction

/-! ### Exact loss of unmarked normalization -/

/-- The normalization `μ ↦ μ/μ(ℝ)`. -/
def normalizeMeasure (μ : Measure ℝ) : Measure ℝ := (μ univ)⁻¹ • μ

/-- **Corollary 4.2**: normalization forgets the absolute scale: `c μ` and `μ` have the same
normalized law for every `0 < c < ∞`, although `c μ ≠ μ` when `μ` is a nonzero finite measure and
`c ≠ 1`. -/
theorem normalizeMeasure_smul (μ : Measure ℝ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    normalizeMeasure (c • μ) = normalizeMeasure μ := by
  rw [normalizeMeasure, normalizeMeasure, Measure.smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_assoc, mul_comm ((μ univ)⁻¹) c, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem smul_ne_self (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {c : ℝ≥0∞} (hc : c ≠ 1) :
    c • μ ≠ μ := by
  intro h
  have h1 := congrArg (fun ν : Measure ℝ => ν univ) h
  simp only [Measure.smul_apply, smul_eq_mul] at h1
  have hne : μ univ ≠ 0 := by rwa [Ne, Measure.measure_univ_eq_zero]
  have := (ENNReal.mul_eq_right hne (measure_ne_top μ univ)).1 h1
  exact hc this

end GaloisForLFunctions.HTGeometry.FormationExcess
