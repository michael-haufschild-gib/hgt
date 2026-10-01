import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality

/-!
# Linear-programming duality for the Weil cone

Fix a level `A`, put `M = ⌊e^{2A}⌋`, and let `w : ℕ → ℝ` vanish beyond `M`. Consider the linear
functional `L_w(lam) = Σ_{2≤n≤M} w(n) lam(n)/√n` on weight systems.

Call a finite family of polar-constrained `C²` tests `f_i` at levels `≤ A`, with weights `α_i ≥ 0`,
**`w`-matched with multiplier `t ≥ 0`** if its combined atom coefficients are
`2π Σ_i α_i atomCoeff(f_i, n) = t w(n)` for every `n ≥ 2`.

* **Weak duality** (`mul_linearWeightSum_le_of_weilPositiveUpTo`). If `lam` is Weil-positive up to level
  `A`, every `w`-matched family has `t L_w(lam) ≤ Σ_i α_i A(f_i)`, where `A(f)` is the archimedean
  energy. On a matched family the weights enter only through `L_w`.
* **Strong duality** (`exists_weilPositiveUpTo_ge_of_weilDualBound`). Suppose every `w`-matched family at
  levels `≤ A + 1` has `t β ≤ Σ_i α_i A(f_i)` (`WeilDualBound`). Then some `lam`, Weil-positive up to
  level `A`, has `β ≤ L_w(lam)`.

So `sup {L_w(lam) : lam Weil-positive up to level A}` is the infimum of archimedean energy per unit of
matched atom mass, up to the level shift `A ↦ A + 1`. Only the archimedean symbol of `ζ` and the
positions `log n` enter. Prime-blind archimedean positivity (`exists_weilPositiveUpTo_of_primeBlindPositive`)
is the case `w = 0`. Every linear extremal problem over the Weil cone, such as uniqueness of the
weights or bounds for harmonic sums, is in this way an archimedean minimization over test families
with prescribed atom coefficients.

**Proof of strong duality.** If no weight system in the compact box `|lam(n)| ≤ √n (log n + C₀)`
works, finitely many tests together with the constraint `L_w ≥ β` already exclude the box.
Hahn–Banach separation gives weights `α ≥ 0` on the tests and `α₀ ≥ 0` on the constraint, whose
combined affine form is negative on the box. At the worst box corner this is
`Σ α_i A(f_i) + 2π Σ_n (log n + C₀) |C'_n| < α₀ β`, where
`C'_n = Σ_i α_i atomCoeff(f_i, n) − α₀ w(n)/(2π)`. One two-point resonator per atom cancels `C'_n`, at
the cost of at most that corner. The resulting family is `w`-matched with multiplier `α₀` and has
archimedean energy `< α₀ β`, which contradicts `WeilDualBound`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

/-- The linear functional `L_w(lam) = Σ_{2≤n≤M} w(n) lam(n)/√n`. -/
def linearWeightSum (M : ℕ) (w lam : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * w n

/-- **The dual bound at level `A`.** Every family of polar tests at levels `≤ A` with weights `α ≥ 0`
whose atom coefficients equal `t w(n)` (`t ≥ 0`) has archimedean energy at least `t β`. -/
def WeilDualBound (A : ℝ) (w : ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ) (t : ℝ),
    (∀ i, a i ≤ A) → (∀ i, IsPolarTest (a i) (f i)) → (∀ i, 0 ≤ α i) → 0 ≤ t →
    (∀ n : ℕ, 2 ≤ n → 2 * π * ∑ i, α i * atomCoeff (f i) n = t * w n) →
    t * β ≤ ∑ i, α i * archEnergy (f i)

/-- **Weak duality.** If `lam` is Weil-positive up to level `A` and a family at levels `≤ A` is
`w`-matched with multiplier `t`, then `t L_w(lam) ≤ Σ α_i A(f_i)`. -/
theorem mul_linearWeightSum_le_of_weilPositiveUpTo {lam : ℕ → ℝ} {A : ℝ}
    (hW : WeilPositiveUpTo lam A) (w : ℕ → ℝ) {ι : Type} [Fintype ι] (a : ι → ℝ)
    (f : ι → ℝ → ℂ) (α : ι → ℝ) (t : ℝ) (ha : ∀ i, a i ≤ A) (hf : ∀ i, IsPolarTest (a i) (f i))
    (hα : ∀ i, 0 ≤ α i)
    (hmatch : ∀ n : ℕ, 2 ≤ n → 2 * π * ∑ i, α i * atomCoeff (f i) n = t * w n) :
    t * linearWeightSum ⌊Real.exp (2 * A)⌋₊ w lam ≤ ∑ i, α i * archEnergy (f i) := by
  set M := ⌊Real.exp (2 * A)⌋₊
  have hM : ∀ i, ⌊Real.exp (2 * a i)⌋₊ ≤ M := fun i =>
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [ha i]))
  have hE : ∀ i, 0 ≤ archEnergy (f i) -
      2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * atomCoeff (f i) n := by
    intro i
    obtain ⟨ha0, hf2, hfs, hp, hm⟩ := hf i
    rw [← integral_weilAtomSymbol_eq_archEnergy_sub hf2 hfs lam (hM i)]
    exact hW (a i) ha0 (ha i) (f i) hf2 hfs hp hm
  have hsum := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hα i) (hE i)
  rw [sum_mul_energy_eq] at hsum
  have hL : 2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * ∑ i, α i * atomCoeff (f i) n =
      t * linearWeightSum M w lam := by
    unfold linearWeightSum
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have h := hmatch n (Finset.mem_Icc.mp hn).1
    calc 2 * π * (lam n / Real.sqrt n * ∑ i, α i * atomCoeff (f i) n)
        = lam n / Real.sqrt n * (2 * π * ∑ i, α i * atomCoeff (f i) n) := by ring
      _ = t * (lam n / Real.sqrt n * w n) := by rw [h]; ring
  linarith

/-- **Strong duality.** If `w` vanishes beyond `M = ⌊e^{2A}⌋` and the dual bound holds at level
`A + 1`, then some weight system Weil-positive up to level `A` has `L_w(lam) ≥ β`. -/
theorem exists_weilPositiveUpTo_ge_of_weilDualBound {A : ℝ} {w : ℕ → ℝ} {β : ℝ}
    (hw : ∀ n, ⌊Real.exp (2 * A)⌋₊ < n → w n = 0) (hD : WeilDualBound (A + 1) w β) :
    ∃ lam : ℕ → ℝ, WeilPositiveUpTo lam A ∧ β ≤ linearWeightSum ⌊Real.exp (2 * A)⌋₊ w lam := by
  classical
  set M := ⌊Real.exp (2 * A)⌋₊ with hMdef
  let T := {p : ℝ × (ℝ → ℂ) // p.1 ≤ A ∧ IsPolarTest p.1 p.2}
  let E : T → (ℕ → ℝ) → ℝ := fun p lam =>
    archEnergy p.1.2 - 2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * atomCoeff p.1.2 n
  set L : (ℕ → ℝ) → ℝ := fun lam => linearWeightSum M w lam with hLdef
  set B : Set (ℕ → ℝ) := Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) with hBdef
  have hBc : IsCompact B := isCompact_univ_pi fun n => isCompact_Icc
  have hBconv : Convex ℝ B := convex_pi fun n _ => convex_Icc _ _
  have hEcont : ∀ p : T, Continuous (E p) := fun p =>
    continuous_const.sub (continuous_const.mul (continuous_finsetSum _ fun n _ =>
      ((continuous_apply n).div_const _).mul_const _))
  have hLcont : Continuous L :=
    continuous_finsetSum _ fun n _ => ((continuous_apply n).div_const _).mul_const _
  -- the closed constraints: the tests and the linear bound
  let K : Option T → Set (ℕ → ℝ) := fun o => match o with
    | some p => {lam | 0 ≤ E p lam}
    | none => {lam | β ≤ L lam}
  have hKc : ∀ o, IsClosed (K o) := by
    rintro (_ | p)
    · exact isClosed_le continuous_const hLcont
    · exact isClosed_le continuous_const (hEcont p)
  have hMle : ∀ p : T, ⌊Real.exp (2 * p.1.1)⌋₊ ≤ M := fun p =>
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [p.2.1]))
  suffices hne : (B ∩ ⋂ o, K o).Nonempty by
    obtain ⟨lam, -, hlam⟩ := hne
    refine ⟨lam, fun a ha haA f hf hfs hp hm => ?_, Set.mem_iInter.mp hlam none⟩
    have hmem := Set.mem_iInter.mp hlam (some ⟨(a, f), haA, ha, hf, hfs, hp, hm⟩)
    rw [integral_weilAtomSymbol_eq_archEnergy_sub hf hfs lam
      (hMle ⟨(a, f), haA, ha, hf, hfs, hp, hm⟩)]
    exact hmem
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  obtain ⟨u, hu⟩ := hBc.elim_finite_subfamily_closed K hKc hemp
  let us : Finset T := u.preimage some (fun _ _ _ _ h => Option.some_injective _ h)
  have hexcl : ∀ lam ∈ B, (∀ p ∈ us, 0 ≤ E p lam) → β ≤ L lam → False := by
    intro lam hlam hE hL
    have hmem : lam ∈ B ∩ ⋂ o ∈ u, K o := by
      refine ⟨hlam, Set.mem_iInter₂.mpr fun o ho => ?_⟩
      rcases o with _ | p
      · exact hL
      · exact hE p (Finset.mem_preimage.mpr ho)
    rw [hu] at hmem
    exact hmem
  -- the affine forms of the constraints, indexed by `Option us`
  let F : Option ↥us → (ℕ → ℝ) → ℝ := fun o lam => match o with
    | some p => E p.1 lam
    | none => L lam - β
  have hFaff : ∀ (o : Option ↥us) (l₁ l₂ : ℕ → ℝ) (a b : ℝ), a + b = 1 →
      F o (a • l₁ + b • l₂) = a * F o l₁ + b * F o l₂ := by
    rintro (_ | p) l₁ l₂ a b hab
    · simp only [F, hLdef, linearWeightSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hs : ∑ n ∈ Finset.Icc 2 M, (a * l₁ n + b * l₂ n) / Real.sqrt n * w n =
          a * ∑ n ∈ Finset.Icc 2 M, l₁ n / Real.sqrt n * w n +
            b * ∑ n ∈ Finset.Icc 2 M, l₂ n / Real.sqrt n * w n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [hs]
      linear_combination β * hab
    · simp only [F, E, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hs : ∑ n ∈ Finset.Icc 2 M, (a * l₁ n + b * l₂ n) / Real.sqrt n *
          atomCoeff p.1.1.2 n =
          a * ∑ n ∈ Finset.Icc 2 M, l₁ n / Real.sqrt n * atomCoeff p.1.1.2 n +
            b * ∑ n ∈ Finset.Icc 2 M, l₂ n / Real.sqrt n * atomCoeff p.1.1.2 n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [hs]
      linear_combination (-archEnergy p.1.1.2) * hab
  have hFcont : ∀ o, Continuous (F o) := by
    rintro (_ | p)
    · exact hLcont.sub continuous_const
    · exact hEcont p.1
  let Φ : (ℕ → ℝ) → (Option ↥us → ℝ) := fun lam o => F o lam
  set C : Set (Option ↥us → ℝ) := Φ '' B with hCdef
  set O : Set (Option ↥us → ℝ) := Set.univ.pi fun _ => Ici (0 : ℝ) with hOdef
  have hCconv : Convex ℝ C := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    obtain ⟨l₁, hl₁, rfl⟩ := hy₁
    obtain ⟨l₂, hl₂, rfl⟩ := hy₂
    refine ⟨a • l₁ + b • l₂, hBconv hl₁ hl₂ ha hb hab, ?_⟩
    funext o
    simp only [Φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hFaff o l₁ l₂ a b hab]
  have hCc : IsCompact C := hBc.image (continuous_pi fun o => hFcont o)
  have hOconv : Convex ℝ O := convex_pi fun _ _ => convex_Ici 0
  have hOc : IsClosed O := isClosed_set_pi fun _ _ => isClosed_Ici
  have hdisj : Disjoint C O := by
    rw [Set.disjoint_left]
    rintro y ⟨lam, hlam, rfl⟩ hO
    have hO' := Set.mem_univ_pi.mp hO
    refine hexcl lam hlam (fun p hp => (hO' (some ⟨p, hp⟩) : 0 ≤ E p lam)) ?_
    have h0 : 0 ≤ L lam - β := hO' none
    linarith
  obtain ⟨φ, u₀, v₀, hφC, huv, hφO⟩ :=
    geometric_hahn_banach_compact_closed hCconv hCc hOconv hOc hdisj
  have hv₀ : v₀ < 0 := by
    have := hφO 0 (Set.mem_univ_pi.mpr fun _ => Set.mem_Ici.mpr le_rfl)
    rwa [map_zero] at this
  let α : Option ↥us → ℝ := fun o => φ fun j => if o = j then 1 else 0
  have hα : ∀ o, 0 ≤ α o := by
    intro o
    by_contra h
    push Not at h
    have hmem : (v₀ / α o) • (fun j : Option ↥us => if o = j then (1 : ℝ) else 0) ∈ O := by
      refine Set.mem_univ_pi.mpr fun j => Set.mem_Ici.mpr ?_
      have : 0 ≤ v₀ / α o := (div_pos_of_neg_of_neg hv₀ h).le
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp [this]
    have := hφO _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne] at this
    exact lt_irrefl _ this
  have hφsum : ∀ y : Option ↥us → ℝ, φ y = ∑ o, α o * y o := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (φ : (Option ↥us → ℝ) →ₗ[ℝ] ℝ) y
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  set α₀ : ℝ := α none with hα₀def
  have hneg : ∀ lam ∈ B,
      ∑ p : ↥us, α (some p) * E p.1 lam + α₀ * (L lam - β) < 0 := by
    intro lam hlam
    have := hφC (Φ lam) ⟨lam, hlam, rfl⟩
    rw [hφsum, Fintype.sum_option] at this
    simp only [Φ, F] at this
    linarith
  -- the worst box corner
  let Cn : ℕ → ℝ := fun n => ∑ p : ↥us, α (some p) * atomCoeff p.1.1.2 n - α₀ * w n / (2 * π)
  let lamS : ℕ → ℝ := fun n => if 0 ≤ Cn n then -boxWidth n else boxWidth n
  have hlamS : lamS ∈ B := by
    refine Set.mem_univ_pi.mpr fun n => ?_
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [lamS, mem_Icc]
    split_ifs <;> constructor <;> linarith
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hcorner : ∑ p : ↥us, α (some p) * E p.1 lamS + α₀ * (L lamS - β) =
      ∑ p : ↥us, α (some p) * archEnergy p.1.1.2 +
        2 * π * ∑ n ∈ Finset.Icc 2 M, (Real.log n + boxConst) * |Cn n| - α₀ * β := by
    have h := sum_mul_energy_eq (fun p : ↥us => p.1.1.2) (fun p => α (some p)) lamS M
    simp only [E]
    rw [h]
    have hterm : ∀ n ∈ Finset.Icc 2 M, lamS n / Real.sqrt n * Cn n =
        -((Real.log n + boxConst) * |Cn n|) := by
      intro n hn
      have hn2 := (Finset.mem_Icc.mp hn).1
      rw [← boxWidth_div_sqrt hn2]
      simp only [lamS]
      split_ifs with hc
      · rw [abs_of_nonneg hc]; ring
      · rw [abs_of_neg (not_le.mp hc)]; ring
    have hexp : 2 * π * ∑ n ∈ Finset.Icc 2 M, lamS n / Real.sqrt n *
        ∑ p : ↥us, α (some p) * atomCoeff p.1.1.2 n - α₀ * L lamS =
        2 * π * ∑ n ∈ Finset.Icc 2 M, lamS n / Real.sqrt n * Cn n := by
      simp only [hLdef, linearWeightSum, Cn]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hexp
    linarith
  -- the matched family: the tests of `us` and one resonator per atom
  let sgn : ℕ → ℝ := fun n => if 0 ≤ Cn n then -1 else 1
  have hsgn : ∀ n, sgn n = 1 ∨ sgn n = -1 := fun n => by
    simp only [sgn]; split_ifs <;> simp
  let aF : ↥us ⊕ ↥(Finset.Icc 2 M) → ℝ :=
    Sum.elim (fun p => p.1.1.1) (fun n => atomLevel n.1)
  let fF : ↥us ⊕ ↥(Finset.Icc 2 M) → ℝ → ℂ :=
    Sum.elim (fun p => p.1.1.2) (fun n => twoPointResonator n.1 (sgn n.1))
  let αF : ↥us ⊕ ↥(Finset.Icc 2 M) → ℝ :=
    Sum.elim (fun p => α (some p)) (fun n => |Cn n.1| / (2 * resonatorMass n.1))
  have hlev : ∀ x, aF x ≤ A + 1 := by
    rintro (p | n)
    · show p.1.1.1 ≤ A + 1
      linarith [p.1.2.1]
    · exact atomLevel_le (Finset.mem_Icc.mp n.2).1 (Finset.mem_Icc.mp n.2).2
  have hpol : ∀ x, IsPolarTest (aF x) (fF x) := by
    rintro (p | n)
    · exact p.1.2.2
    · exact isPolarTest_twoPointResonator (Finset.mem_Icc.mp n.2).1 _
  have hwt : ∀ x, 0 ≤ αF x := by
    rintro (p | n)
    · exact hα _
    · exact div_nonneg (abs_nonneg _) (by have := resonatorMass_pos n.1; positivity)
  have hmatch : ∀ m : ℕ, 2 ≤ m → 2 * π * ∑ x, αF x * atomCoeff (fF x) m = α₀ * w m := by
    intro m hm
    rw [Fintype.sum_sum_type]
    have hres : ∑ n : ↥(Finset.Icc 2 M), αF (Sum.inr n) * atomCoeff (fF (Sum.inr n)) m =
        ∑ n ∈ Finset.Icc 2 M, (if m = n then |Cn n| * sgn n else 0) := by
      rw [← Finset.sum_coe_sort (Finset.Icc 2 M)]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hn2 := (Finset.mem_Icc.mp n.2).1
      have hk := resonatorMass_pos n.1
      simp only [αF, fF, Sum.elim_inr]
      rw [atomCoeff_twoPointResonator hn2 _ hm]
      split_ifs
      · field_simp
      · simp
    rw [hres, Finset.sum_ite_eq]
    have hus : ∑ p : ↥us, αF (Sum.inl p) * atomCoeff (fF (Sum.inl p)) m =
        ∑ p : ↥us, α (some p) * atomCoeff p.1.1.2 m := rfl
    rw [hus]
    split_ifs with hmM
    · have hCm : ∑ p : ↥us, α (some p) * atomCoeff p.1.1.2 m = Cn m + α₀ * w m / (2 * π) := by
        simp only [Cn]; ring
      rw [hCm]
      simp only [sgn]
      split_ifs with hc
      · rw [abs_of_nonneg hc]; field_simp; ring
      · rw [abs_of_neg (not_le.mp hc)]; field_simp; ring
    · have hMm : M < m := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmM
        rcases hmM with h | h
        · omega
        · exact h
      have : ∑ p : ↥us, α (some p) * atomCoeff p.1.1.2 m = 0 := Finset.sum_eq_zero fun p _ => by
        rw [atomCoeff_eq_zero_of_floor_lt p.1.2.2.2.2.1 (lt_of_le_of_lt (hMle p.1) hMm),
          mul_zero]
      rw [this, add_zero, mul_zero, hw m hMm, mul_zero]
  have hdual := hD _ aF fF αF α₀ hlev hpol hwt (hα none) hmatch
  rw [Fintype.sum_sum_type] at hdual
  have hres : ∑ n : ↥(Finset.Icc 2 M), αF (Sum.inr n) * archEnergy (fF (Sum.inr n)) ≤
      2 * π * ∑ n ∈ Finset.Icc 2 M, (Real.log n + boxConst) * |Cn n| := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (Finset.Icc 2 M)]
    refine Finset.sum_le_sum fun n _ => ?_
    have hn2 := (Finset.mem_Icc.mp n.2).1
    have hk := resonatorMass_pos n.1
    simp only [αF, fF, Sum.elim_inr]
    have hle := archEnergy_twoPointResonator_le hn2 (hsgn n.1)
    have hc : 0 ≤ |Cn n.1| / (2 * resonatorMass n.1) :=
      div_nonneg (abs_nonneg _) (by positivity)
    calc |Cn n.1| / (2 * resonatorMass n.1) * archEnergy (twoPointResonator n.1 (sgn n.1))
        ≤ |Cn n.1| / (2 * resonatorMass n.1) *
            (4 * π * resonatorMass n.1 * (Real.log n.1 + boxConst)) :=
          mul_le_mul_of_nonneg_left hle hc
      _ = 2 * π * ((Real.log n.1 + boxConst) * |Cn n.1|) := by field_simp; ring
  have hsumu : ∑ p : ↥us, αF (Sum.inl p) * archEnergy (fF (Sum.inl p)) =
      ∑ p : ↥us, α (some p) * archEnergy p.1.1.2 := rfl
  have := hneg lamS hlamS
  rw [hcorner] at this
  linarith

/-- **The dual bound is necessary.** If some weight system Weil-positive up to level `A` has
`L_w(lam) ≥ β`, then the dual bound holds at level `A`. -/
theorem weilDualBound_of_weilPositiveUpTo {A : ℝ} {w : ℕ → ℝ} {β : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveUpTo lam A) (hβ : β ≤ linearWeightSum ⌊Real.exp (2 * A)⌋₊ w lam) :
    WeilDualBound A w β := by
  intro ι _ a f α t ha hf hα ht hmatch
  have h := mul_linearWeightSum_le_of_weilPositiveUpTo hW w a f α t ha hf hα hmatch
  nlinarith [mul_le_mul_of_nonneg_left hβ ht]

/-! ## All levels -/

theorem linearWeightSum_eq_of_le {N M : ℕ} (hNM : N ≤ M) {w : ℕ → ℝ} (hw : ∀ n, N < n → w n = 0)
    (lam : ℕ → ℝ) : linearWeightSum M w lam = linearWeightSum N w lam := by
  unfold linearWeightSum
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hNM) fun n hn hnot => ?_).symm
  have : N < n := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with h | h
    · exact absurd (Finset.mem_Icc.mp hn).1 (by omega)
    · exact h
  rw [hw n this, mul_zero]

/-- **Linear-programming duality for the Weil cone, all levels.** Let `w` vanish beyond `N`. Some
Weil-positive weight system has `L_w(lam) ≥ β` iff the dual bound holds at every level `A` with
`⌊e^{2A}⌋ ≥ N`. -/
theorem exists_weilPositive_ge_iff_forall_weilDualBound {N : ℕ} {w : ℕ → ℝ} {β : ℝ}
    (hw : ∀ n, N < n → w n = 0) :
    (∃ lam : ℕ → ℝ, WeilPositive lam ∧ β ≤ linearWeightSum N w lam) ↔
      ∀ A : ℝ, N ≤ ⌊Real.exp (2 * A)⌋₊ → WeilDualBound A w β := by
  constructor
  · rintro ⟨lam, hlam, hβ⟩ A hA
    refine weilDualBound_of_weilPositiveUpTo (lam := lam)
      (fun a ha _ f hf hfs hp hm => hlam a ha f hf hfs hp hm) ?_
    rw [linearWeightSum_eq_of_le hA hw]
    exact hβ
  intro hD
  -- the level `k` with `⌊e^{2k}⌋ ≥ N` for `k ≥ N`
  have hlev : ∀ k : ℕ, N ≤ k → N ≤ ⌊Real.exp (2 * (k : ℝ))⌋₊ := by
    intro k hk
    refine Nat.le_floor ?_
    have h1 : (k : ℝ) + 1 ≤ Real.exp (k : ℝ) := Real.add_one_le_exp _
    have h2 : Real.exp (k : ℝ) ≤ Real.exp (2 * (k : ℝ)) :=
      Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hex : ∀ k : ℕ, ∃ lam : ℕ → ℝ, WeilPositiveUpTo lam ((k + N : ℕ) : ℝ) ∧
      β ≤ linearWeightSum N w lam := by
    intro k
    have hk := hlev (k + N) (by omega)
    have hk1 : N ≤ ⌊Real.exp (2 * (((k + N : ℕ) : ℝ) + 1))⌋₊ :=
      hk.trans (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))
    obtain ⟨lam, hlam, hβ⟩ := exists_weilPositiveUpTo_ge_of_weilDualBound
      (fun n hn => hw n (lt_of_le_of_lt hk hn)) (hD _ hk1)
    exact ⟨lam, hlam, by rwa [linearWeightSum_eq_of_le hk hw] at hβ⟩
  choose lam hlam hβ using hex
  -- clamp into the box
  set clamp : ℕ → ℕ → ℝ := fun k n => max (-boxWidth n) (min (boxWidth n) (lam k n)) with hclamp
  have hK : IsCompact (Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ k, clamp k ∈ Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) := by
    intro k n _
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [hclamp, mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  obtain ⟨lam₀, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hcoord : ∀ n, Tendsto (fun j => clamp (φ j) n) atTop (𝓝 (lam₀ n)) :=
    fun n => tendsto_pi_nhds.mp hlim n
  have hagree : ∀ n, 2 ≤ n → ∀ᶠ j in atTop, clamp (φ j) n = lam (φ j) n := by
    intro n hn
    obtain ⟨K, hK⟩ := exists_nat_ge (atomLevel n)
    filter_upwards [(hφ.tendsto_atTop.eventually_ge_atTop K)] with j hj
    have hlev' : atomLevel n ≤ ((φ j + N : ℕ) : ℝ) :=
      hK.trans (by exact_mod_cast (show K ≤ φ j + N by omega))
    have hbox := abs_le_boxWidth_of_weilPositiveUpTo (hlam (φ j)) hn hlev'
    rw [abs_le] at hbox
    simp only [hclamp]
    rw [min_eq_right hbox.2, max_eq_right hbox.1]
  refine ⟨lam₀, fun a ha f hf hfs hp hm => ?_, ?_⟩
  · set M := ⌊Real.exp (2 * a)⌋₊ with hM
    set c : ℕ → ℝ := fun n => (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re
    set E : (ℕ → ℝ) → ℝ := fun l =>
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
        2 * π * ∑ n ∈ Finset.Icc 2 M, l n / Real.sqrt n * c n with hE
    have hEq : ∀ l, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol l M (τ / (2 * π)) = E l :=
      fun l => integral_weilAtomSymbol_eq_affine hf hfs l
    have hElim : Tendsto (fun j => E (clamp (φ j))) atTop (𝓝 (E lam₀)) := by
      simp only [hE]
      refine tendsto_const_nhds.sub (Tendsto.const_mul _ (tendsto_finsetSum _ fun n _ => ?_))
      exact ((hcoord n).div_const _).mul_const _
    have hEagree : ∀ᶠ j in atTop, E (clamp (φ j)) = E (lam (φ j)) := by
      have hall : ∀ᶠ j in atTop, ∀ n ∈ Finset.Icc 2 M, clamp (φ j) n = lam (φ j) n :=
        (Finset.eventually_all _).mpr fun n hn => hagree n (Finset.mem_Icc.mp hn).1
      filter_upwards [hall] with j hj
      simp only [hE]
      congr 2
      exact Finset.sum_congr rfl fun n hn => by rw [hj n hn]
    have hEpos : ∀ᶠ j in atTop, 0 ≤ E (clamp (φ j)) := by
      obtain ⟨K, hK⟩ := exists_nat_ge a
      filter_upwards [hEagree, hφ.tendsto_atTop.eventually_ge_atTop K] with j hj hjK
      rw [hj, ← hEq]
      exact hlam (φ j) a ha (hK.trans (by exact_mod_cast (show K ≤ φ j + N by omega)))
        f hf hfs hp hm
    rw [hEq]
    exact ge_of_tendsto hElim hEpos
  · have hLlim : Tendsto (fun j => linearWeightSum N w (clamp (φ j))) atTop
        (𝓝 (linearWeightSum N w lam₀)) := by
      unfold linearWeightSum
      exact tendsto_finsetSum _ fun n _ => ((hcoord n).div_const _).mul_const _
    have hLagree : ∀ᶠ j in atTop, linearWeightSum N w (clamp (φ j)) =
        linearWeightSum N w (lam (φ j)) := by
      have hall : ∀ᶠ j in atTop, ∀ n ∈ Finset.Icc 2 N, clamp (φ j) n = lam (φ j) n :=
        (Finset.eventually_all _).mpr fun n hn => hagree n (Finset.mem_Icc.mp hn).1
      filter_upwards [hall] with j hj
      unfold linearWeightSum
      exact Finset.sum_congr rfl fun n hn => by rw [hj n hn]
    refine ge_of_tendsto hLlim ?_
    filter_upwards [hLagree] with j hj
    rw [hj]
    exact hβ (φ j)

/-- The single-atom weight `w = √n₀ · 1_{n₀}`, for which `L_w(lam) = lam(n₀)`. -/
def singleAtomWeight (n₀ : ℕ) : ℕ → ℝ := fun n => if n = n₀ then Real.sqrt n₀ else 0

theorem linearWeightSum_singleAtomWeight {n₀ N : ℕ} (hn₀ : 2 ≤ n₀) (hN : n₀ ≤ N)
    (lam : ℕ → ℝ) : linearWeightSum N (singleAtomWeight n₀) lam = lam n₀ := by
  unfold linearWeightSum singleAtomWeight
  rw [Finset.sum_eq_single n₀ (fun n _ hn => by rw [if_neg hn, mul_zero])
    (fun h => absurd (Finset.mem_Icc.mpr ⟨hn₀, hN⟩) h), if_pos rfl]
  have hs : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  field_simp

/-- **The range of one weight over the Weil cone.** Some Weil-positive weight system has
`lam(n₀) ≥ β` iff at every level seeing `n₀`, every family of polar tests whose combined atom
coefficients vanish at all `n ≠ n₀` and equal `t √n₀/(2π)` at `n₀` has archimedean energy `≥ t β`.
So the weight `n₀` is pinned across the Weil cone exactly when such single-atom families have
archimedean energy per unit atom arbitrarily close to the extreme values. -/
theorem exists_weilPositive_weight_ge_iff {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {β : ℝ} :
    (∃ lam : ℕ → ℝ, WeilPositive lam ∧ β ≤ lam n₀) ↔
      ∀ A : ℝ, n₀ ≤ ⌊Real.exp (2 * A)⌋₊ → WeilDualBound A (singleAtomWeight n₀) β := by
  have hw : ∀ n, n₀ < n → singleAtomWeight n₀ n = 0 := fun n hn => by
    unfold singleAtomWeight; rw [if_neg (by omega)]
  rw [← exists_weilPositive_ge_iff_forall_weilDualBound hw]
  simp only [linearWeightSum_singleAtomWeight hn₀ le_rfl]

end RHTower
