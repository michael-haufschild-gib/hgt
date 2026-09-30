import GaloisForLFunctions.RHTower.WeilFullConeWindowPinning

/-!
# Compactness of the Weil cone and the finite-prefix criterion

Let `C` be the set of full-cone Weil-positive sequences `lam : ℕ → ℝ`, normalized by
`lam 0 = lam 1 = 0` (these values never enter the Weil functional).

**Theorems.**
- `exists_abs_le_of_weilPositiveFull`. Every coordinate is bounded uniformly over `C`: for each
  `n ≥ 2` there is `b_n` with `|lam(n)| ≤ b_n` for every Weil-positive `lam`.
- `isClosed_setOf_weilPositiveFull` and `isCompact_normalizedWeilCone`. `C` is closed in the product
  topology, and the normalized cone is compact.
- `riemannHypothesis_iff_forall_prefix`. RH holds iff for every `N` some Weil-positive sequence
  agrees with `Λ` on `2 ≤ n ≤ N`. Each finite prefix of `Λ` extends to a Weil-positive system, and
  compactness glues the extensions.

**Proofs.**
- The bound is window pinning with a bump `g` of radius `1/(4(n+1))` at `L = log n`. The window
  then isolates the single coordinate `n`: `S_L(lam) = lam(n) ρ(0)/√n`.
- Closedness holds because each Weil condition involves finitely many coordinates.
- Compactness is Tychonoff's theorem.
- The criterion follows by nested compact sets.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## Narrow bumps isolate one coordinate -/

theorem autoCorr_eq_zero_of_radius {g : ℝ → ℝ} {r : ℝ} (hsupp : ∀ u, r < |u| → g u = 0)
    {x : ℝ} (hx : 2 * r < |x|) : autoCorr g x = 0 := by
  unfold autoCorr
  have h0 : (fun t => g t * g (t - x)) = fun _ => 0 := by
    funext t
    rcases le_or_gt |t| r with ht | ht
    · have : r < |t - x| := by
        have := abs_sub_abs_le_abs_sub x t
        rw [abs_sub_comm] at this; linarith
      simp [hsupp _ this]
    · simp [hsupp t ht]
  rw [h0, integral_zero]

/-- The real narrow bump of radius `1/(4(n+1))`. -/
def narrowG (n : ℕ) (u : ℝ) : ℝ := narrowBump n u

theorem narrowG_eq_zero (n : ℕ) {u : ℝ} (hu : 1 / (4 * ((n : ℝ) + 1)) < |u|) : narrowG n u = 0 :=
  (narrowBump n).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hu.le)

theorem narrowG_supp (n : ℕ) : ∀ u, 1 / 4 < |u| → narrowG n u = 0 := fun u hu =>
  narrowG_eq_zero n (lt_of_le_of_lt (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hu)

theorem contDiff_narrowG (n : ℕ) : ContDiff ℝ 2 (narrowG n) :=
  (narrowBump n).contDiff

theorem hasCompactSupport_narrowG (n : ℕ) : HasCompactSupport (narrowG n) :=
  (narrowBump n).hasCompactSupport

theorem autoCorr_narrowG_zero_pos (n : ℕ) : 0 < autoCorr (narrowG n) 0 := by
  have h := integral_narrowBump_sq_pos n
  unfold autoCorr narrowG
  simpa [sq] using h

/-- At `L = log n` the narrow window vector is the single coordinate `n`. -/
theorem windowVector_narrowG {n : ℕ} (hn : 2 ≤ n) :
    windowVector (contDiff_narrowG n) (hasCompactSupport_narrowG n) (narrowG_supp n)
        (Real.log n) =
      Finsupp.single ⟨n, hn⟩ (autoCorr (narrowG n) 0 / Real.sqrt n) := by
  have hsupp := fun u (hu : 1 / (4 * ((n : ℝ) + 1)) < |u|) => narrowG_eq_zero n hu
  have hr : 2 * (1 / (4 * ((n : ℝ) + 1))) = 1 / (2 * ((n : ℝ) + 1)) := by field_simp; ring
  have hsmall : 1 / (2 * ((n : ℝ) + 1)) < Real.log 2 := by
    refine lt_of_le_of_lt ?_ WeilExcess.seventeen_div_twentyfive_lt_log_two
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hpos : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  ext m
  simp only [windowVector, Finsupp.ofSupportFinite_coe, windowValue, Finsupp.single_apply]
  have hm2 : Real.log 2 ≤ Real.log (m : ℕ) :=
    Real.log_le_log two_pos (by exact_mod_cast m.2)
  have hn2 : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have e2 : autoCorr (narrowG n) (Real.log (m : ℕ) + Real.log n) = 0 :=
    autoCorr_eq_zero_of_radius hsupp (by rw [hr, abs_of_pos (by linarith)]; linarith)
  rw [e2, add_zero]
  by_cases h : (m : ℕ) = n
  · rw [if_pos (Subtype.ext h).symm, h, sub_self]
  · rw [if_neg fun h' => h (congrArg Subtype.val h').symm]
    have hgap := WeilExcess.inv_succ_le_abs_log_sub (by have := m.2; omega) (by omega) h
    have hlt : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    rw [autoCorr_eq_zero_of_radius hsupp (by rw [hr]; linarith), zero_div]

/-- **Uniform coordinate bounds on the Weil cone.** -/
theorem exists_abs_le_of_weilPositiveFull {n : ℕ} (hn : 2 ≤ n) :
    ∃ b : ℝ, ∀ lam : ℕ → ℝ, WeilPositiveFull lam → |lam n| ≤ b := by
  obtain ⟨C, hC⟩ := exists_abs_windowSum_sub_le (contDiff_narrowG n) (hasCompactSupport_narrowG n)
    (narrowG_supp n)
  set c := autoCorr (narrowG n) 0 / Real.sqrt n with hc
  have hc0 : 0 < c := div_pos (autoCorr_narrowG_zero_pos n)
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))
  set M := 2 * (∫ u, narrowG n u * Real.exp (-u / 2)) * (∫ u, narrowG n u * Real.exp (u / 2)) *
    Real.cosh (Real.log n / 2) with hM
  refine ⟨(|M| + C) / c, fun lam hW => ?_⟩
  have h := hC lam hW (Real.log n)
  rw [windowSum, windowVector_narrowG hn, linearCombination_single, smul_eq_mul, ← hM] at h
  rw [le_div_iff₀ hc0]
  have h1 := abs_sub_abs_le_abs_sub (c * lam n) M
  rw [abs_mul, abs_of_pos hc0] at h1
  linarith [le_abs_self M]

/-! ## Closedness and compactness -/

theorem continuous_re_weilFullFunctional (f : WeilTestFn) :
    Continuous fun lam : ℕ → ℝ => (weilFullFunctional lam (EF.weilTest f.1 f.1)).re := by
  have e : (fun lam : ℕ → ℝ => (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) =
      fun lam => weilArchRe (EF.weilTest f.1 f.1) -
        ∑ j ∈ (logVector f).support, logVector f j * lam j := by
    funext lam
    rw [re_weilFullFunctional_eq, linearCombination_apply, Finsupp.sum]
    simp only [smul_eq_mul]
  rw [e]
  exact continuous_const.sub (continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_apply _))

/-- **The Weil cone is closed** in the product topology. -/
theorem isClosed_setOf_weilPositiveFull : IsClosed {lam : ℕ → ℝ | WeilPositiveFull lam} := by
  have e : {lam : ℕ → ℝ | WeilPositiveFull lam} =
      ⋂ f : WeilTestFn, {lam | 0 ≤ (weilFullFunctional lam (EF.weilTest f.1 f.1)).re} := by
    ext lam
    simp only [mem_setOf_eq, mem_iInter]
    exact ⟨fun h f => h f.1 f.2.1 f.2.2, fun h f hf hc => h ⟨f, hf, hc⟩⟩
  rw [e]
  exact isClosed_iInter fun f => isClosed_le continuous_const (continuous_re_weilFullFunctional f)

/-- The coordinate bound, chosen for every index (zero below `2`). -/
def weilConeBound (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then Classical.choose (exists_abs_le_of_weilPositiveFull hn) else 0

theorem abs_le_weilConeBound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (h01 : ∀ n, n < 2 → lam n = 0) (n : ℕ) : |lam n| ≤ weilConeBound n := by
  unfold weilConeBound
  split_ifs with hn
  · exact Classical.choose_spec (exists_abs_le_of_weilPositiveFull hn) lam hW
  · rw [h01 n (by omega), abs_zero]

/-- The normalized Weil cone. -/
def normalizedWeilCone : Set (ℕ → ℝ) :=
  {lam | WeilPositiveFull lam ∧ ∀ n, n < 2 → lam n = 0}

theorem isClosed_normalizedWeilCone : IsClosed normalizedWeilCone := by
  have e : normalizedWeilCone = {lam : ℕ → ℝ | WeilPositiveFull lam} ∩
      ⋂ n : ℕ, ⋂ (_ : n < 2), {lam : ℕ → ℝ | lam n = 0} := by
    ext lam; simp [normalizedWeilCone]
  rw [e]
  exact isClosed_setOf_weilPositiveFull.inter (isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply n) continuous_const)

/-- **The normalized Weil cone is compact.** -/
theorem isCompact_normalizedWeilCone : IsCompact normalizedWeilCone := by
  refine (isCompact_univ_pi (s := fun n => Icc (-weilConeBound n) (weilConeBound n))
    fun n => isCompact_Icc).of_isClosed_subset isClosed_normalizedWeilCone fun lam hlam => ?_
  simp only [Set.mem_pi, mem_univ, true_implies, mem_Icc]
  intro n
  exact abs_le.mp (abs_le_weilConeBound hlam.1 hlam.2 n)

/-! ## The finite-prefix criterion -/

/-- **RH is a statement about finite prefixes.** RH holds iff for every `N` some full-cone
Weil-positive sequence agrees with `Λ` on `2 ≤ n ≤ N`. -/
theorem riemannHypothesis_iff_forall_prefix :
    RiemannHypothesis ↔ ∀ N : ℕ, ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      ∀ n, 2 ≤ n → n ≤ N → lam n = ArithmeticFunction.vonMangoldt n := by
  constructor
  · intro hRH N
    exact ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, fun _ _ _ => rfl⟩
  · intro h
    set t : ℕ → Set (ℕ → ℝ) := fun N => normalizedWeilCone ∩
      ⋂ n : ℕ, ⋂ (_ : 2 ≤ n ∧ n ≤ N),
        {lam : ℕ → ℝ | lam n = ArithmeticFunction.vonMangoldt n} with ht
    have hsub : ∀ N, t (N + 1) ⊆ t N := by
      intro N lam hlam
      refine ⟨hlam.1, ?_⟩
      have h2 := hlam.2
      simp only [mem_iInter, mem_setOf_eq, and_imp] at h2 ⊢
      intro n hn1 hn2
      exact h2 n hn1 (by omega)
    have hne : ∀ N, (t N).Nonempty := by
      intro N
      obtain ⟨lam, hW, hagree⟩ := h N
      refine ⟨fun n => if n < 2 then 0 else lam n, ⟨?_, fun n hn => by simp [hn]⟩, ?_⟩
      · intro f hf hc
        have := hW f hf hc
        rwa [weilFullFunctional_congr (lam' := fun n => if n < 2 then 0 else lam n)
          (fun n hn => by simp [show ¬ n < 2 by omega])] at this
      · simp only [mem_iInter, mem_setOf_eq, and_imp]
        intro n hn1 hn2
        rw [if_neg (by omega)]
        exact hagree n hn1 hn2
    have hcl : ∀ N, IsClosed (t N) := fun N =>
      isClosed_normalizedWeilCone.inter (isClosed_iInter fun n => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply n) continuous_const)
    have hc0 : IsCompact (t 0) :=
      isCompact_normalizedWeilCone.of_isClosed_subset (hcl 0) inter_subset_left
    obtain ⟨lam, hlam⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hsub hne hc0 hcl
    simp only [mem_iInter] at hlam
    have hW : WeilPositiveFull lam := (hlam 0).1.1
    have heq : ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
      intro n hn
      have := (hlam n).2
      simp only [mem_iInter, mem_setOf_eq, and_imp] at this
      exact this n hn le_rfl
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_
    have := hW f hf hc
    rwa [weilFullFunctional_congr heq] at this

end

end RHTower.WeilOneSided
