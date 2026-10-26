import GaloisForLFunctions.MultiplicativePositivityGeometry.FamilyBochner
import GaloisForLFunctions.MultiplicativePositivityGeometry.LocallyFiniteBochner

/-!
# Bochner's theorem for locally finite family configurations

A configuration `𝒟` on `G × ℝ` is *locally finite* if each `{p : 𝒟 p ≠ 0, |p₂| ≤ R}` is finite. For
a family over a finite abelian group `G`, a locally finite `𝒟` is a joint boundary divisor iff it is
even and positive definite on `G × ℝ` (`family_locallyFinite_bochner`). Poles and zeros may sit at
infinitely many points of `G × ℝ`, on any members.

* **Range** (`isJointBoundaryDivisor_of_tendsto_famPosCosPoly`). A pointwise limit of family cosine
  polynomials `Σ_i c_i Re(ψ_i(g) e^{iλ_i u})`, `c_i ≥ 0`, is a joint boundary divisor.
* **Fejér truncation** (`IsEvenPosDef.mul_fejerFactor_comp`). `𝒟(g, v)(1 − |v|/N)⁺` stays positive
  definite (overlaps of intervals along the height), and it is finitely supported, so its family
  Bohr series is nonnegative.
* **Smoothing** (`famPoly_eq`). The family cosine polynomial with coefficients
  `B_N(ψ, k/n)/(n²|G|)` at the frequencies `(ψ, k/n)` equals, by character orthogonality, the
  truncation convolved with the Dirichlet mean `Q_n` along each fibre; taking `n` large against
  the number of points, it converges to `𝒟` at every point.
-/

open Finset Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

universe u

/-! ### Fejér truncation along a height -/

section Fejer

variable {Γ : Type*} [AddCommGroup Γ]

/-- **Fejér truncation along a height preserves positive definiteness.** -/
theorem IsEvenPosDef.mul_fejerFactor_comp {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (π : Γ →+ ℝ) {N : ℝ}
    (hN : 0 < N) : IsEvenPosDef fun γ => φ γ * fejerFactor N (π γ) where
  even u := by simp only [map_neg, fejerFactor, abs_neg, hφ.even]
  posDef n x c := by
    set f : Fin n → ℝ → ℝ := fun i => (Set.Icc (π (x i)) (π (x i) + N)).indicator 1
    have hint : ∀ i j, Integrable fun t => f i t * f j t := fun i j => by
      have hfun : (fun t => f i t * f j t) =
          (Set.Icc (π (x i)) (π (x i) + N) ∩ Set.Icc (π (x j)) (π (x j) + N)).indicator 1 := by
        simp only [f]; rw [Set.inter_indicator_one]; rfl
      rw [hfun]
      exact (continuous_one.integrableOn_Icc.mono_set Set.inter_subset_left).integrable_indicator
        (measurableSet_Icc.inter measurableSet_Icc)
    have key : ∑ i, ∑ j, c i * c j * (φ (x i - x j) * fejerFactor N (π (x i - x j))) =
        N⁻¹ * ∫ t, ∑ i, ∑ j, c i * f i t * (c j * f j t) * φ (x i - x j) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (((hint i j).const_mul (c i * c j)).mul_const (φ (x i - x j))).congr
            (Eventually.of_forall fun t => by ring), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ =>
          (((hint i j).const_mul (c i * c j)).mul_const (φ (x i - x j))).congr
            (Eventually.of_forall fun t => by ring), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (fun t => c i * f i t * (c j * f j t) * φ (x i - x j)) =
          fun t => c i * c j * φ (x i - x j) * (f i t * f j t) by funext t; ring,
        integral_const_mul, integral_indicator_mul_indicator hN, map_sub]
      field_simp
    rw [key]
    exact mul_nonneg (inv_nonneg.mpr hN.le)
      (integral_nonneg fun t => hφ.posDef n x fun i => c i * f i t)

end Fejer

variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ### Family cosine polynomials -/

/-- A family cosine polynomial `Σ_i c_i Re(ψ_i(g) e^{iλ_i u})` with `c_i ≥ 0`. -/
def IsFamPosCosPoly (P : G × ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (c lam : ℕ → ℝ) (ψ : ℕ → AddChar G ℂ), (∀ i, 0 ≤ c i) ∧
    ∀ q, P q = ∑ i ∈ range N, c i * jointMode (ψ i) (lam i) q

omit [Fintype G] [DecidableEq G] in
theorem isFamPosCosPoly_finset_sum {ι : Type*} (s : Finset ι) (c lam : ι → ℝ)
    (ψ : ι → AddChar G ℂ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    IsFamPosCosPoly fun q => ∑ i ∈ s, c i * jointMode (ψ i) (lam i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => le_rfl, fun q => by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, c', lam', ψ', hc', hrep⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
    refine ⟨N + 1, fun j => if j = N then c a else c' j, fun j => if j = N then lam a else lam' j,
      fun j => if j = N then ψ a else ψ' j, fun j => ?_, fun q => ?_⟩
    · beta_reduce
      split_ifs
      · exact hc a (Finset.mem_insert_self a s)
      · exact hc' j
    · beta_reduce
      have hr := hrep q
      beta_reduce at hr
      rw [Finset.sum_insert ha, hr, Finset.sum_range_succ, if_pos rfl, if_pos rfl, if_pos rfl,
        add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≠ N := (Finset.mem_range.mp hj).ne
      rw [if_neg this, if_neg this, if_neg this]

omit [Fintype G] [DecidableEq G] in
/-- **Range.** A pointwise limit of family cosine polynomials is a joint boundary divisor. -/
theorem isJointBoundaryDivisor_of_tendsto_famPosCosPoly {P : ℕ → G × ℝ → ℝ} {𝒟 : G × ℝ → ℝ}
    (hP : ∀ n, IsFamPosCosPoly (P n)) (hlim : ∀ q, Tendsto (fun n => P n q) atTop (𝓝 (𝒟 q))) :
    ∃ (ψ : ℕ × ℕ → AddChar G ℂ) (lam : ℕ × ℕ → ℝ) (w : ℝ → ℕ × ℕ → ℝ),
      IsJointBoundaryDivisor ψ lam w 𝒟 := by
  classical
  choose N c lam ψ hc hrep using hP
  set n₀ : ℝ → ℕ := fun x => ⌊1 / x⌋₊
  set w : ℝ → ℕ × ℕ → ℝ := fun x p =>
    if p.1 = n₀ x ∧ p.2 < N p.1 then c p.1 p.2 / x else 0
  have hsupp : ∀ x, ∀ p ∉ ({n₀ x} : Finset ℕ) ×ˢ range (N (n₀ x)), w x p = 0 := by
    intro x p hp
    simp only [w]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hp (Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr h1,
      Finset.mem_range.mpr (h1 ▸ h2)⟩)
  have htrace : ∀ x, 0 < x → ∀ q, x * jointTrace (w x) (fun p => ψ p.1 p.2)
      (fun p => lam p.1 p.2) q = P (n₀ x) q := by
    intro x hx q
    unfold jointTrace
    rw [tsum_eq_sum (s := ({n₀ x} : Finset ℕ) ×ˢ range (N (n₀ x))) fun p hp => by
      rw [hsupp x p hp, zero_mul], Finset.sum_product, Finset.sum_singleton, hrep, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [w, if_pos (And.intro rfl (Finset.mem_range.mp hi))]
    field_simp
  refine ⟨fun p => ψ p.1 p.2, fun p => lam p.1 p.2, w, ⟨fun x hx p => ?_, fun x _ => ?_,
    fun q => ?_⟩⟩
  · simp only [w]
    split_ifs
    · exact div_nonneg (hc _ _) hx.le
    · exact le_rfl
  · exact summable_of_ne_finset_zero (hsupp x)
  · have h1 : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    have hn : Tendsto n₀ (𝓝[>] 0) atTop := tendsto_nat_floor_atTop.comp h1
    refine ((hlim q).comp hn).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (htrace x hx q).symm

/-! ### Smoothing a finite family configuration -/

/-- The family cosine polynomial of a configuration with Bohr series `B`, at mesh `1/n`. -/
noncomputable def famPoly (E : G × ℝ → ℝ) (n : ℕ) (q : G × ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (n ^ 2), ∑ ψ : AddChar G ℂ,
    1 / ((n : ℝ) ^ 2 * Fintype.card G) * familyBohr E ψ ((k : ℝ) / n) *
      jointMode ψ ((k : ℝ) / n) q

omit [DecidableEq G] in
theorem famPoly_isFamPosCosPoly {E : G × ℝ → ℝ} (hE : IsEvenPosDef E) (hs : Summable E)
    (n : ℕ) : IsFamPosCosPoly (famPoly E n) := by
  have h := isFamPosCosPoly_finset_sum (G := G) (Icc 1 (n ^ 2) ×ˢ (Finset.univ : Finset (AddChar G ℂ)))
    (fun r => 1 / ((n : ℝ) ^ 2 * Fintype.card G) * familyBohr E r.2 ((r.1 : ℝ) / n))
    (fun r => (r.1 : ℝ) / n) (fun r => r.2)
    (fun r _ => mul_nonneg (by positivity) (familyBohr_nonneg hE hs _ _))
  convert h using 2 with q
  rw [famPoly, Finset.sum_product]

/-- **Character orthogonality at one frequency.** For a configuration supported in a finite set `S`,
`Σ_ψ B(ψ, t) Re(ψ(g) e^{itu})/|G| = Σ_{p ∈ S} (E(p)/2)([g = p₁] cos t(u − p₂) + [g = −p₁] cos t(u + p₂))`. -/
theorem sum_familyBohr_mul_jointMode {E : G × ℝ → ℝ} {S : Finset (G × ℝ)}
    (hS : ∀ p ∉ S, E p = 0) (t : ℝ) (q : G × ℝ) :
    ∑ ψ : AddChar G ℂ, 1 / (Fintype.card G : ℝ) * familyBohr E ψ t * jointMode ψ t q =
      ∑ p ∈ S, E p / 2 * ((if q.1 = p.1 then 1 else 0) * Real.cos (t * (q.2 - p.2)) +
        (if q.1 = -p.1 then 1 else 0) * Real.cos (t * (q.2 + p.2))) := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hbohr : ∀ ψ, familyBohr E ψ t = ∑ p ∈ S, E p * jointMode ψ t (-p) := fun ψ => by
    unfold familyBohr
    exact tsum_eq_sum fun p hp => by rw [hS p hp, zero_mul]
  simp only [hbohr]
  have e : ∀ ψ : AddChar G ℂ, 1 / (Fintype.card G : ℝ) *
      (∑ p ∈ S, E p * jointMode ψ t (-p)) * jointMode ψ t q =
      ∑ p ∈ S, E p / Fintype.card G * (jointMode ψ t (-p) * jointMode ψ t q) := fun ψ => by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun ψ _ => e ψ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, sum_jointMode_mul]
  field_simp

/-- **Smoothing by character orthogonality.** For a configuration supported in a finite set `S`,
the family polynomial is the fibrewise convolution with the Dirichlet mean. -/
theorem famPoly_eq {E : G × ℝ → ℝ} {S : Finset (G × ℝ)} (hS : ∀ p ∉ S, E p = 0) (n : ℕ)
    (q : G × ℝ) :
    famPoly E n q = ∑ p ∈ S, E p / 2 * ((if q.1 = p.1 then 1 else 0) *
        dirichletMean n (q.2 - p.2) + (if q.1 = -p.1 then 1 else 0) * dirichletMean n (q.2 + p.2)) := by
  have hone := sum_familyBohr_mul_jointMode hS (q := q)
  unfold dirichletMean
  have e2 : ∀ k : ℕ, ∑ ψ : AddChar G ℂ, 1 / ((n : ℝ) ^ 2 * Fintype.card G) *
      familyBohr E ψ ((k : ℝ) / n) * jointMode ψ ((k : ℝ) / n) q =
      1 / (n : ℝ) ^ 2 * ∑ ψ : AddChar G ℂ, 1 / (Fintype.card G : ℝ) *
        familyBohr E ψ ((k : ℝ) / n) * jointMode ψ ((k : ℝ) / n) q := fun k => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ψ _ => by ring
  have hL : famPoly E n q = ∑ k ∈ Icc 1 (n ^ 2), ∑ p ∈ S, E p / 2 *
      ((if q.1 = p.1 then 1 else 0) * (1 / (n : ℝ) ^ 2 * Real.cos ((k : ℝ) / n * (q.2 - p.2))) +
        (if q.1 = -p.1 then 1 else 0) *
          (1 / (n : ℝ) ^ 2 * Real.cos ((k : ℝ) / n * (q.2 + p.2)))) := by
    unfold famPoly
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [e2, hone, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

/-! ### Locally finite family configurations -/

variable {𝒟 : G × ℝ → ℝ}

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- Around a height `u`, the nonzero shifts `u ∓ p₂` by points of a locally finite configuration stay
at a positive distance from `0`. -/
theorem exists_famGap (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) (u : ℝ) :
    ∃ δ > 0, ∀ p, 𝒟 p ≠ 0 → (u - p.2 = 0 ∨ δ ≤ |u - p.2|) ∧ (u + p.2 = 0 ∨ δ ≤ |u + p.2|) := by
  classical
  set F := (hloc (|u| + 1)).toFinset
  set V : Finset ℝ :=
    ((F.image fun p => |u - p.2|) ∪ (F.image fun p => |u + p.2|)).filter (0 < ·)
  obtain ⟨m, hm0, hmV⟩ : ∃ m > 0, ∀ v ∈ V, m ≤ v := by
    by_cases hV : V.Nonempty
    · obtain ⟨m, hmV, hmin⟩ := V.exists_min_image id hV
      exact ⟨m, (Finset.mem_filter.mp hmV).2, fun v hv => hmin v hv⟩
    · exact ⟨1, one_pos, fun v hv => absurd ⟨v, hv⟩ hV⟩
  refine ⟨min 1 m, lt_min one_pos hm0, fun p hp => ?_⟩
  by_cases hpb : |p.2| ≤ |u| + 1
  · have hpF : p ∈ F := (Set.Finite.mem_toFinset _).mpr ⟨hp, hpb⟩
    constructor
    · by_cases h0 : u - p.2 = 0
      · exact Or.inl h0
      · exact Or.inr ((min_le_right _ _).trans (hmV _ (Finset.mem_filter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hpF), abs_pos.mpr h0⟩)))
    · by_cases h0 : u + p.2 = 0
      · exact Or.inl h0
      · exact Or.inr ((min_le_right _ _).trans (hmV _ (Finset.mem_filter.mpr
          ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpF), abs_pos.mpr h0⟩)))
  · have h1 : 1 ≤ |u - p.2| := by
      have := abs_sub_abs_le_abs_sub p.2 u
      rw [abs_sub_comm] at this
      linarith
    have h2 : 1 ≤ |u + p.2| := by
      have := abs_sub_abs_le_abs_sub p.2 (-u)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith
    exact ⟨Or.inr ((min_le_left _ _).trans h1), Or.inr ((min_le_left _ _).trans h2)⟩

/-- The points with `|p₂| ≤ N + 1` carrying `𝒟`. -/
noncomputable def famSupport (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite)
    (N : ℕ) : Finset (G × ℝ) :=
  (hloc ((N : ℝ) + 1)).toFinset

/-- The Fejér truncation `𝒟(p)(1 − |p₂|/(N + 1))⁺`. -/
noncomputable def famConfig (𝒟 : G × ℝ → ℝ) (N : ℕ) (p : G × ℝ) : ℝ :=
  𝒟 p * fejerFactor ((N : ℝ) + 1) p.2

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem famConfig_eq_zero (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) (N : ℕ)
    {p : G × ℝ} (hp : p ∉ famSupport hloc N) : famConfig 𝒟 N p = 0 := by
  unfold famConfig
  by_cases h𝒟 : 𝒟 p = 0
  · rw [h𝒟, zero_mul]
  · have hb : ¬ |p.2| ≤ (N : ℝ) + 1 := fun hb =>
      hp ((Set.Finite.mem_toFinset _).mpr ⟨h𝒟, hb⟩)
    rw [fejerFactor_eq_zero (by positivity) (not_le.mp hb).le, mul_zero]

omit [Fintype G] [DecidableEq G] in
theorem famConfig_isEvenPosDef' (h𝒟 : IsEvenPosDef 𝒟) (N : ℕ) : IsEvenPosDef (famConfig 𝒟 N) :=
  h𝒟.mul_fejerFactor_comp (AddMonoidHom.snd G ℝ) (by positivity)

omit [Fintype G] [DecidableEq G] in
theorem abs_famConfig_le (h𝒟 : IsEvenPosDef 𝒟) (N : ℕ) (p : G × ℝ) : |famConfig 𝒟 N p| ≤ 𝒟 0 := by
  unfold famConfig
  rw [abs_mul, abs_of_nonneg (fejerFactor_nonneg _ _)]
  exact (mul_le_of_le_one_right (abs_nonneg _) (fejerFactor_le_one (by positivity) _)).trans
    (h𝒟.abs_le_apply_zero p)

/-- The smoothing order `(N + 1)(1 + #S_N)`. -/
noncomputable def famOrder (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite)
    (N : ℕ) : ℕ :=
  (N + 1) * (1 + (famSupport hloc N).card)

/-- The approximating family cosine polynomials. -/
noncomputable def famApprox (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite)
    (N : ℕ) : G × ℝ → ℝ :=
  famPoly (famConfig 𝒟 N) (famOrder hloc N)

omit [Fintype G] in
/-- The point masses at `q` and `−q` through the fibre indicators. -/
theorem fibre_dirac (q p : G × ℝ) :
    ((if q.1 = p.1 then (1 : ℝ) else 0) * diracAt (q.2 - p.2) = if p = q then 1 else 0) ∧
    ((if q.1 = -p.1 then (1 : ℝ) else 0) * diracAt (q.2 + p.2) = if p = -q then 1 else 0) := by
  constructor
  · unfold diracAt
    by_cases h : p = q
    · subst h; simp
    · rw [if_neg h]
      by_cases h1 : q.1 = p.1
      · rw [if_pos h1, if_neg (fun h2 => h (Prod.ext h1.symm (by linarith [sub_eq_zero.mp h2]))),
          mul_zero]
      · rw [if_neg h1, zero_mul]
  · unfold diracAt
    by_cases h : p = -q
    · subst h; simp
    · rw [if_neg h]
      by_cases h1 : q.1 = -p.1
      · rw [if_pos h1, if_neg (fun h2 => h (Prod.ext (by rw [Prod.fst_neg, h1, neg_neg])
          (by simp only [Prod.snd_neg]; linarith [add_eq_zero_iff_eq_neg.mp h2]))), mul_zero]
      · rw [if_neg h1, zero_mul]

/-- The smoothing error at `q`, once `|q₂| ≤ N`, is at most `𝒟(0) π/((N + 1) δ)`. -/
theorem abs_famApprox_sub_le (h𝒟 : IsEvenPosDef 𝒟)
    (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) {q : G × ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ p, 𝒟 p ≠ 0 → (q.2 - p.2 = 0 ∨ δ ≤ |q.2 - p.2|) ∧ (q.2 + p.2 = 0 ∨ δ ≤ |q.2 + p.2|))
    {N : ℕ} (hN : |q.2| ≤ N) :
    |famApprox hloc N q - famConfig 𝒟 N q| ≤ 𝒟 0 * Real.pi / (((N : ℝ) + 1) * δ) := by
  classical
  set S := famSupport hloc N
  set E := famConfig 𝒟 N
  set n := famOrder hloc N
  have hS : ∀ p ∉ S, E p = 0 := fun p hp => famConfig_eq_zero hloc N hp
  have hn : 0 < n := by unfold n famOrder; positivity
  have hnR : (n : ℝ) = ((N : ℝ) + 1) * (1 + S.card) := by
    simp only [n, famOrder]; push_cast; ring
  have hNn : (N : ℝ) + 1 ≤ n := by
    rw [hnR]; nlinarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ _)]
  have hD0 := h𝒟.apply_zero_nonneg
  set B := Real.pi / (n * δ)
  -- `E(q)` as a sum of point masses over `S`.
  have hEq : E q = ∑ p ∈ S, E p / 2 * ((if q.1 = p.1 then 1 else 0) * diracAt (q.2 - p.2) +
      (if q.1 = -p.1 then 1 else 0) * diracAt (q.2 + p.2)) := by
    have hEven : E (-q) = E q := (famConfig_isEvenPosDef' h𝒟 N).even q
    have e : ∀ p, E p / 2 * ((if q.1 = p.1 then 1 else 0) * diracAt (q.2 - p.2) +
        (if q.1 = -p.1 then 1 else 0) * diracAt (q.2 + p.2)) =
        (if p = q then E p / 2 else 0) + (if p = -q then E p / 2 else 0) := fun p => by
      rw [(fibre_dirac q p).1, (fibre_dirac q p).2]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    by_cases hq : q ∈ S <;> by_cases hq' : -q ∈ S
    · rw [if_pos hq, if_pos hq', hEven]; ring
    · have h1 := hS _ hq'
      rw [hEven] at h1
      rw [if_pos hq, if_neg hq', h1]; ring
    · have h1 := hS _ hq
      rw [if_neg hq, if_pos hq', hEven, h1]; ring
    · rw [if_neg hq, if_neg hq', hS _ hq]; ring
  -- The kernel error at each relevant shift.
  have hY : ∀ p ∈ S, ∀ w, (w = q.2 - p.2 ∨ w = q.2 + p.2) →
      |dirichletMean n w - diracAt w| ≤ B := by
    intro p hp w hw
    have hpS := (Set.Finite.mem_toFinset _).mp hp
    by_cases hw0 : w = 0
    · rw [hw0, dirichletMean_zero hn, diracAt, if_pos rfl, sub_self, abs_zero]
      positivity
    · have hgw : δ ≤ |w| := by
        rcases hw with rfl | rfl
        · exact ((hgap p hpS.1).1.resolve_left hw0)
        · exact ((hgap p hpS.1).2.resolve_left hw0)
      have hwb : |w| ≤ Real.pi * n := by
        have : |w| ≤ |q.2| + |p.2| := by
          rcases hw with rfl | rfl
          · exact abs_sub _ _
          · exact abs_add_le _ _
        nlinarith [Real.pi_gt_three, hpS.2]
      rw [diracAt, if_neg hw0, sub_zero]
      refine (abs_dirichletMean_le hn (abs_pos.mpr hw0) hwb).trans ?_
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
        (mul_le_mul_of_nonneg_left hgw (by positivity))
  have hdiff : famApprox hloc N q - E q = ∑ p ∈ S, E p / 2 *
      ((if q.1 = p.1 then 1 else 0) * (dirichletMean n (q.2 - p.2) - diracAt (q.2 - p.2)) +
        (if q.1 = -p.1 then 1 else 0) * (dirichletMean n (q.2 + p.2) - diracAt (q.2 + p.2))) := by
    rw [famApprox, famPoly_eq hS, hEq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hdiff]
  have hterm : ∀ p ∈ S, |E p / 2 *
      ((if q.1 = p.1 then 1 else 0) * (dirichletMean n (q.2 - p.2) - diracAt (q.2 - p.2)) +
        (if q.1 = -p.1 then 1 else 0) * (dirichletMean n (q.2 + p.2) - diracAt (q.2 + p.2)))| ≤
      𝒟 0 * B := by
    intro p hp
    have hi1 : |(if q.1 = p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have hi2 : |(if q.1 = -p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have h1 := hY p hp _ (Or.inl rfl)
    have h2 := hY p hp _ (Or.inr rfl)
    have hB0 : 0 ≤ B := by positivity
    rw [abs_mul, abs_div, abs_two]
    have hin : |(if q.1 = p.1 then (1 : ℝ) else 0) *
        (dirichletMean n (q.2 - p.2) - diracAt (q.2 - p.2)) +
        (if q.1 = -p.1 then (1 : ℝ) else 0) *
          (dirichletMean n (q.2 + p.2) - diracAt (q.2 + p.2))| ≤ 2 * B := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul (if q.1 = p.1 then (1 : ℝ) else 0), abs_mul (if q.1 = -p.1 then (1 : ℝ) else 0)]
      have := mul_le_mul hi1 h1 (abs_nonneg _) zero_le_one
      have := mul_le_mul hi2 h2 (abs_nonneg _) zero_le_one
      linarith
    calc |E p| / 2 * |(if q.1 = p.1 then (1 : ℝ) else 0) *
          (dirichletMean n (q.2 - p.2) - diracAt (q.2 - p.2)) +
          (if q.1 = -p.1 then (1 : ℝ) else 0) *
            (dirichletMean n (q.2 + p.2) - diracAt (q.2 + p.2))|
        ≤ 𝒟 0 / 2 * (2 * B) :=
          mul_le_mul (by linarith [abs_famConfig_le h𝒟 N p]) hin (abs_nonneg _) (by positivity)
      _ = 𝒟 0 * B := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hle : (S.card : ℝ) ≤ 1 + S.card := by linarith
  calc (S.card : ℝ) * (𝒟 0 * B) ≤ (1 + S.card) * (𝒟 0 * B) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 𝒟 0 * Real.pi / (((N : ℝ) + 1) * δ) := by
        simp only [B]
        rw [hnR]
        field_simp

/-- **The family polynomials converge to `𝒟` at every point.** -/
theorem tendsto_famApprox (h𝒟 : IsEvenPosDef 𝒟)
    (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) (q : G × ℝ) :
    Tendsto (fun N => famApprox hloc N q) atTop (𝓝 (𝒟 q)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_famGap hloc q.2
  have hE : Tendsto (fun N : ℕ => famConfig 𝒟 N q) atTop (𝓝 (𝒟 q)) := by
    have := (tendsto_fejerFactor q.2).const_mul (𝒟 q)
    rwa [mul_one] at this
  have h0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hB : Tendsto (fun N : ℕ => 𝒟 0 * Real.pi / (((N : ℝ) + 1) * δ)) atTop (𝓝 0) := by
    have h := h0.const_mul (𝒟 0 * Real.pi / δ)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    rw [div_mul_div_comm, mul_one, mul_comm δ]
  have herr : Tendsto (fun N : ℕ => famApprox hloc N q - famConfig 𝒟 N q) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [eventually_ge_atTop ⌈|q.2|⌉₊] with N hN
    rw [Real.norm_eq_abs]
    exact abs_famApprox_sub_le h𝒟 hloc hδ hgap ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  have := hE.add herr
  rw [add_zero] at this
  exact this.congr fun N => by ring

/-- **Bochner's theorem for locally finite family configurations.** A locally finite `𝒟` on
`G × ℝ` is a joint boundary divisor iff it is even and positive definite. -/
theorem family_locallyFinite_bochner
    (hloc : ∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) :
    (∃ (ι : Type) (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) (w : ℝ → ι → ℝ),
        IsJointBoundaryDivisor ψ lam w 𝒟) ↔ IsEvenPosDef 𝒟 := by
  refine ⟨fun ⟨_, _, _, _, hw⟩ => hw.isEvenPosDef, fun h𝒟 => ?_⟩
  have hsum : ∀ N, Summable (famConfig 𝒟 N) := fun N =>
    summable_of_ne_finset_zero (s := famSupport hloc N) fun p hp => famConfig_eq_zero hloc N hp
  obtain ⟨ψ, lam, w, hw⟩ := isJointBoundaryDivisor_of_tendsto_famPosCosPoly
    (fun N => famPoly_isFamPosCosPoly (famConfig_isEvenPosDef' h𝒟 N) (hsum N) (famOrder hloc N))
    (tendsto_famApprox h𝒟 hloc)
  exact ⟨ℕ × ℕ, ψ, lam, w, hw⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
