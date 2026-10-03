import GaloisForLFunctions.RHTower.SoninPolarGroundDiscretization

/-!
# Cofinal admission of the actual prime–polar ground source

The unchanged arithmetic grid has an exact orthogonal annular decomposition
plus its sharp-cutoff terminal vector. Finite total cumulative energy is
equivalent to bounded cofinal returns and to a cofinal strong limit.
Summability selects cutoffs at which the retained endpoint square vanishes.
The admitted within-cell correction transports this criterion to finite
assemblies of the original prime atoms and strong polar integrals.

No upper bound for the actual arithmetic energy is proved here.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower

private def B (a : ℝ) (n : ℕ) : SoninL2 :=
  soninGroundEntry a (Real.log (n+2:ℝ))
private def D (a : ℝ) (n : ℕ) : SoninL2 := B a n-B a (n+1)
private def A (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range (n+1), c j
private def G (a : ℝ) (c : ℕ → ℝ) (n : ℕ) : SoninL2 :=
  ∑ j ∈ range (n+1), (c j:ℂ) • B a j
private def E (c : ℕ → ℝ) (n : ℕ) : ℝ := A c n^2/((n+2:ℝ)*(n+3:ℝ))
private def W (a : ℝ) (c : ℕ → ℝ) (n : ℕ) : SoninL2 := (A c n:ℂ) • D a n

private theorem B_inner (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hij : i ≤ j) :
    inner ℂ (B a i) (B a j) = ((2*a/(j+2:ℝ):ℝ):ℂ) := by
  have hi : (0:ℝ)< i+2 := by positivity
  have hj : (0:ℝ)< j+2 := by positivity
  have hlog : Real.log (i+2:ℝ) ≤ Real.log (j+2:ℝ) :=
    Real.log_le_log hi (by exact_mod_cast Nat.add_le_add_right hij 2)
  rw [B, B, inner_soninGroundEntry_of_le a ha _ _ hlog,
    Real.exp_neg, Real.exp_log hj]
  simp only [div_eq_mul_inv]

private theorem D_B_inner (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hij : i< j) :
    inner ℂ (D a i) (B a j)=0 := by
  rw [D, inner_sub_left, B_inner a ha hij.le, B_inner a ha hij]
  ring

private theorem D_inner_zero (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hij : i≠j) :
    inner ℂ (D a i) (D a j)=0 := by
  wlog hlt : i< j generalizing i j
  · rw [← inner_conj_symm, this hij.symm (by omega), map_zero]
  change inner ℂ (D a i) (B a j-B a (j+1))=0
  rw [inner_sub_right, D_B_inner a ha hlt, D_B_inner a ha (by omega), sub_self]

private theorem B_norm_sq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖B a n‖^2=2*a/(n+2:ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), B_inner a ha le_rfl]
  rfl

private theorem D_norm_sq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖D a n‖^2=2*a/((n+2:ℝ)*(n+3:ℝ)) := by
  rw [D, norm_sub_sq (𝕜 := ℂ), B_norm_sq a ha, B_norm_sq a ha,
    B_inner a ha (Nat.le_succ n)]
  change 2*a/(n+2:ℝ)-2*(2*a/((n+1:ℕ)+2:ℝ))+2*a/((n+1:ℕ)+2:ℝ)=_
  push_cast
  have hn : (n:ℝ)+2≠0 := by positivity
  have hn' : (n:ℝ)+3≠0 := by positivity
  field_simp
  ring

private theorem W_norm_sq (a : ℝ) (ha : 0 ≤ a) (c : ℕ → ℝ) (n : ℕ) :
    ‖W a c n‖^2 = 2*a*E c n := by
  rw [W, norm_smul, mul_pow, D_norm_sq a ha, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  unfold E
  ring

private theorem W_inner_zero (a : ℝ) (ha : 0 ≤ a) (c : ℕ → ℝ) {i j : ℕ} (hij : i≠j) :
    inner ℂ (W a c i) (W a c j)=0 := by
  rw [W, W, inner_smul_left, inner_smul_right, D_inner_zero a ha hij]
  simp

private theorem W_family (a : ℝ) (ha : 0 ≤ a) (c : ℕ → ℝ) :
    OrthogonalFamily ℂ (fun n => Submodule.span ℂ {W a c n})
      (fun n => (Submodule.span ℂ {W a c n}).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro n m hnm
  apply Submodule.isOrtho_span.mpr
  intro u hu v hv
  rw [Set.mem_singleton_iff] at hu hv
  subst u
  subst v
  exact W_inner_zero a ha c hnm

private theorem W_sum_norm_sq (a : ℝ) (ha : 0 ≤ a) (c : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ range (N+1), W a c n‖^2=2*a*∑ n ∈ range (N+1), E c n := by
  let f : ∀ n, Submodule.span ℂ {W a c n} :=
    fun n => ⟨W a c n, Submodule.subset_span (by simp)⟩
  have h := (W_family a ha c).norm_sum f (range (N+1))
  change ‖∑ n ∈ range (N+1), W a c n‖^2=∑ n ∈ range (N+1), ‖W a c n‖^2 at h
  rw [h]
  simp_rw [W_norm_sq a ha]
  exact (Finset.mul_sum _ _ _).symm

private theorem G_decomposition (a : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    G a c N = (∑ n ∈ range (N+1), W a c n)+(A c N:ℂ) • B a (N+1) := by
  induction N with
  | zero => simp [G, W, A, D, smul_sub]
  | succ N ih =>
    have hG : G a c (N+1)=G a c N+(c (N+1):ℂ) • B a (N+1) := by
      exact Finset.sum_range_succ _ _
    have hA : A c (N+1)=A c N+c (N+1) := Finset.sum_range_succ _ _
    rw [hG, ih, Finset.sum_range_succ (fun n => W a c n) (N+1)]
    simp only [W, D, hA]
    push_cast
    simp only [add_smul, smul_sub]
    abel

private theorem G_norm_sq (a : ℝ) (ha : 0 ≤ a) (c : ℕ → ℝ) (N : ℕ) :
    ‖G a c N‖^2=2*a*((∑ n ∈ range (N+1), E c n)+A c N^2/(N+3:ℝ)) := by
  have horth : inner ℂ (∑ n ∈ range (N+1), W a c n) ((A c N:ℂ) • B a (N+1))=0 := by
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro n hn
    rw [W, inner_smul_left, inner_smul_right, D_B_inner a ha (Finset.mem_range.mp hn)]
    simp
  rw [G_decomposition, norm_add_sq (𝕜 := ℂ), horth,
    W_sum_norm_sq a ha, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, B_norm_sq a ha]
  simp only [map_zero, mul_zero, add_zero]
  push_cast
  ring

private theorem E_nonneg (c : ℕ → ℝ) (n : ℕ) : 0 ≤ E c n := by unfold E; positivity

private theorem W_summable (a : ℝ) (ha : 0 ≤ a) (c : ℕ → ℝ) (h : Summable (E c)) :
    Summable (W a c) := by
  let f : ∀ n, Submodule.span ℂ {W a c n} :=
    fun n => ⟨W a c n, Submodule.subset_span (by simp)⟩
  apply ((W_family a ha c).summable_iff_norm_sq_summable f).mpr
  change Summable (fun n => ‖W a c n‖^2)
  simpa only [W_norm_sq a ha] using h.mul_left (2*a)

private theorem terminal_small (c : ℕ → ℝ) (h : Summable (E c)) (ε : ℝ) (hε : 0<ε)
    (M : ℕ) : ∃ N, M≤N ∧ A c N^2/(N+3:ℝ)<ε := by
  by_contra hn
  push Not at hn
  have hs : Summable (fun n : ℕ => 1/(n+2:ℝ)) := by
    apply Summable.of_norm_bounded_eventually_nat (h.div_const ε)
    filter_upwards [eventually_ge_atTop M] with n hMn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ)≤1/(n+2:ℝ))]
    have hA : ε*(n+3:ℝ)≤A c n^2 :=
      (le_div_iff₀ (by positivity : (0:ℝ)< n+3)).mp (hn n hMn)
    calc
      1/(n+2:ℝ) = (ε*(n+3:ℝ))/((n+2:ℝ)*(n+3:ℝ))/ε := by
        field_simp
      _ ≤ E c n/ε :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hA (by positivity)) hε.le
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hs

private theorem cofinal_limit_of_energy (a : ℝ) (ha : 0≤a) (c : ℕ → ℝ)
    (h : Summable (E c)) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      Tendsto (fun k => G a c (φ k)) atTop (𝓝 (∑' n, W a c n)) := by
  have hx (k : ℕ) : ∃ N, k≤N ∧ A c N^2/(N+3:ℝ)<1/(k+1:ℝ) :=
    terminal_small c h _ (by positivity) k
  choose φ hφ₁ hφ₂ using hx
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφ₁ tendsto_id
  have ht : Tendsto (fun k => A c (φ k)^2/(φ k+3:ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun k => by positivity) (fun k => (hφ₂ k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : Tendsto (fun k => ‖(A c (φ k):ℂ) • B a (φ k+1)‖^2) atTop (𝓝 0) := by
    have hh := ht.const_mul (2*a)
    simp only [mul_zero] at hh
    convert hh using 1
    funext k
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, B_norm_sq a ha]
    push_cast
    ring
  have hb : Tendsto (fun k => (A c (φ k):ℂ) • B a (φ k+1)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  have hp := (W_summable a ha c h).hasSum.tendsto_sum_nat.comp
    (tendsto_atTop_mono (fun k => Nat.le_succ (φ k)) hφ)
  refine ⟨φ,hφ,?_⟩
  simpa only [← G_decomposition, add_zero, Function.comp_def] using hp.add hb

private theorem energy_of_bounded_returns (a : ℝ) (ha : 0< a) (c : ℕ → ℝ)
    (h : ∃ C : ℝ, ∀ M : ℕ, ∃ N, M≤N ∧ ‖G a c N‖^2≤C) : Summable (E c) := by
  obtain ⟨C,hC⟩ := h
  apply summable_of_sum_range_le (E_nonneg c) (c := C/(2*a))
  intro M
  obtain ⟨N,hMN,hN⟩ := hC M
  have hle : (∑ n ∈ range M, E c n) ≤ ∑ n ∈ range (N+1), E c n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun n _ _ => E_nonneg c n)
  rw [G_norm_sq a ha.le] at hN
  apply (le_div_iff₀ (by positivity : 0<2*a)).mpr
  have hnn : 0≤A c N^2/(N+3:ℝ) := by positivity
  nlinarith

private theorem bounded_returns_of_cofinal_limit (a : ℝ) (c : ℕ → ℝ)
    (h : ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      ∃ g : SoninL2, Tendsto (fun k => G a c (φ k)) atTop (𝓝 g)) :
    ∃ C : ℝ, ∀ M : ℕ, ∃ N, M≤N ∧ ‖G a c N‖^2≤C := by
  obtain ⟨φ,hφ,g,hg⟩ := h
  obtain ⟨C,hC⟩ := (hg.norm.pow 2).bddAbove_range
  refine ⟨C,fun M => ?_⟩
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hφ.eventually (eventually_ge_atTop M))
  exact ⟨φ k,hk k le_rfl,hC (Set.mem_range_self k)⟩

/-- Actual prime indicator minus the unchanged original polar cell mass. -/
def soninPrimePolarGridCoefficient (n : ℕ) : ℝ :=
  (if (n+2).Prime then 1 else 0)-soninPolarGroundCellMass n

/-- Complete signed arithmetic prefix; every prime and polar cell is retained. -/
def soninPrimePolarGridCumulative (N : ℕ) : ℝ :=
  ∑ n ∈ range (N+1), soninPrimePolarGridCoefficient n

/-- Literal grid source remaining after the admitted within-cell polar correction. -/
def soninPrimePolarGridSource (a : ℝ) (N : ℕ) : SoninL2 :=
  ∑ n ∈ range (N+1), (soninPrimePolarGridCoefficient n:ℂ) •
    soninGroundEntry a (Real.log (n+2:ℝ))

/-- Positive cumulative energy of the actual signed arithmetic source. -/
def soninPrimePolarGridEnergy (n : ℕ) : ℝ :=
  soninPrimePolarGridCumulative n^2/((n+2:ℝ)*(n+3:ℝ))

/-- Exact full energy, including the sharp-cutoff terminal square. -/
theorem soninPrimePolarGridSource_norm_sq (a : ℝ) (ha : 0≤a) (N : ℕ) :
    ‖soninPrimePolarGridSource a N‖^2=2*a*
      ((∑ n ∈ range (N+1), soninPrimePolarGridEnergy n)+
        soninPrimePolarGridCumulative N^2/(N+3:ℝ)) :=
  G_norm_sq a ha soninPrimePolarGridCoefficient N

/-- Cofinal bounded returns are exactly finite total cumulative energy.
No arithmetic upper bound is assumed or supplied by this equivalence. -/
theorem soninPrimePolarGrid_bounded_returns_iff_energy (a : ℝ) (ha : 0< a) :
    (∃ C : ℝ, ∀ M : ℕ, ∃ N, M≤N ∧ ‖soninPrimePolarGridSource a N‖^2≤C) ↔
      Summable soninPrimePolarGridEnergy := by
  constructor
  · exact energy_of_bounded_returns a ha soninPrimePolarGridCoefficient
  · intro h
    obtain ⟨φ,hφ,hg⟩ := cofinal_limit_of_energy a ha.le soninPrimePolarGridCoefficient h
    exact bounded_returns_of_cofinal_limit a soninPrimePolarGridCoefficient ⟨φ,hφ,_,hg⟩

/-- A cofinal strong limit exists exactly when the actual total cumulative energy is finite.
The proof selects cutoffs where the retained terminal vector tends to zero. -/
theorem soninPrimePolarGrid_cofinal_limit_iff_energy (a : ℝ) (ha : 0< a) :
    (∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      ∃ g : SoninL2, Tendsto (fun k => soninPrimePolarGridSource a (φ k)) atTop (𝓝 g)) ↔
        Summable soninPrimePolarGridEnergy := by
  constructor
  · intro h
    exact energy_of_bounded_returns a ha soninPrimePolarGridCoefficient
      (bounded_returns_of_cofinal_limit a soninPrimePolarGridCoefficient h)
  · intro h
    obtain ⟨φ,hφ,hg⟩ := cofinal_limit_of_energy a ha.le soninPrimePolarGridCoefficient h
    exact ⟨φ,hφ,_,hg⟩

/-- Finite total arithmetic energy pays the endpoint square on a cofinal schedule. -/
theorem soninPrimePolarGrid_energy_terminal_selection :
    Summable soninPrimePolarGridEnergy →
      ∀ ε : ℝ, 0<ε → ∀ M : ℕ, ∃ N, M≤N ∧
        soninPrimePolarGridCumulative N^2/(N+3:ℝ)<ε :=
  fun h => terminal_small soninPrimePolarGridCoefficient h

/-- Finite assembly of the literal prime atoms and original strong polar integrals. -/
def soninPrimePolarCellSource (a : ℝ) (N : ℕ) : SoninL2 :=
  ∑ n ∈ range (N+1),
    ((if (n+2).Prime then soninGroundEntry a (Real.log (n+2:ℝ)) else 0)-
      ∫ u in Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ)),
        soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial a 0))

/-- The full original cell assembly differs from its arithmetic grid by the admitted correction. -/
theorem soninPrimePolarCellSource_eq_grid_sub_error (a : ℝ) (N : ℕ) :
    soninPrimePolarCellSource a N = soninPrimePolarGridSource a N-
      ∑ n ∈ range (N+1), soninPolarGroundCellError a n := by
  unfold soninPrimePolarCellSource soninPrimePolarGridSource
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sonin_polar_ground_cell_decomposition]
  unfold soninPrimePolarGridCoefficient
  by_cases hp : (n+2).Prime
  · simp only [hp, if_true, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  · simp only [hp, if_false, zero_sub, Complex.ofReal_neg, neg_smul]
    abel

/-- The cofinal strong-admission criterion retains the original prime atoms and all polar cells.
The remaining unproved arithmetic task is summability of the displayed cumulative energy. -/
theorem soninPrimePolarCellSource_cofinal_limit_iff_energy (a : ℝ) (ha : 0 < a) :
    (∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      ∃ g : SoninL2, Tendsto (fun k => soninPrimePolarCellSource a (φ k)) atTop (𝓝 g)) ↔
        Summable soninPrimePolarGridEnergy := by
  have he := (summable_soninPolarGroundCellError a ha.le).hasSum.tendsto_sum_nat
  constructor
  · rintro ⟨φ,hφ,g,hg⟩
    apply (soninPrimePolarGrid_cofinal_limit_iff_energy a ha).mp
    refine ⟨φ,hφ,g+∑' n, soninPolarGroundCellError a n,?_⟩
    have hh := hg.add (he.comp (tendsto_atTop_mono (fun k => Nat.le_succ (φ k)) hφ))
    simpa only [soninPrimePolarCellSource_eq_grid_sub_error, sub_add_cancel,
      Function.comp_def] using hh
  · intro h
    obtain ⟨φ,hφ,g,hg⟩ := (soninPrimePolarGrid_cofinal_limit_iff_energy a ha).mpr h
    refine ⟨φ,hφ,g-∑' n, soninPolarGroundCellError a n,?_⟩
    have hh := hg.sub (he.comp (tendsto_atTop_mono (fun k => Nat.le_succ (φ k)) hφ))
    simpa only [soninPrimePolarCellSource_eq_grid_sub_error, Function.comp_def] using hh

end RHTower
