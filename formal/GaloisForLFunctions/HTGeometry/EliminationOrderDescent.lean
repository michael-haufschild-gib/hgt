import GaloisForLFunctions.HTGeometry.PointwiseGradedIndependence

/-!
# The elimination strictly lowers the order

Two members of equal blow-up order admit a combination whose leading value cancels.  For that
combination to be usable one needs to know that its order is *strictly* smaller — otherwise the
elimination could loop.  It is: the order along a chart is unique, and a function whose leading
value cancels at order `m` cannot have a nonzero leading value at any order `≥ m`.

Together with the invertibility of the elementary recombination, this is what makes the search for a
separating basis terminate: the total order of the family drops at every step and cannot drop below
zero.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## Order along a chart -/

/-- `f` has blow-up order `m` with nonzero leading value `C` along the chart `(u, t)`. -/
def GradedAlong (f : ℂ → ℂ) (u t : ℕ → ℂ) (m : ℕ) (C : ℂ) : Prop :=
  C ≠ 0 ∧ Tendsto (fun j => f (u j) * t j ^ m) atTop (𝓝 C)

/-- **The order along a chart is unique.** -/
theorem gradedAlong_order_unique {f : ℂ → ℂ} {u t : ℕ → ℂ} {m m' : ℕ} {C C' : ℂ}
    (ht : Tendsto t atTop (𝓝 0)) (h : GradedAlong f u t m C) (h' : GradedAlong f u t m' C') :
    m = m' := by
  obtain ⟨hC, hlim⟩ := h
  obtain ⟨hC', hlim'⟩ := h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hpow : Tendsto (fun j => t j ^ (m' - m)) atTop (𝓝 0) := by
      have hp := ht.pow (m' - m)
      rwa [zero_pow (by omega)] at hp
    have hmul := hlim.mul hpow
    rw [mul_zero] at hmul
    refine hC' (tendsto_nhds_unique hlim' ?_)
    refine hmul.congr fun j => ?_
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
  · have hpow : Tendsto (fun j => t j ^ (m - m')) atTop (𝓝 0) := by
      have hp := ht.pow (m - m')
      rwa [zero_pow (by omega)] at hp
    have hmul := hlim'.mul hpow
    rw [mul_zero] at hmul
    refine hC (tendsto_nhds_unique hlim ?_)
    refine hmul.congr fun j => ?_
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]

/-- **The elimination has strictly smaller order.**  Its leading value cancels at order `m`, so no
order `≥ m` can carry a nonzero leading value. -/
theorem order_lt_of_leadingElimination {f g : ℂ → ℂ} {u t : ℕ → ℂ} {m m' : ℕ} {α β C' : ℂ}
    (ht : Tendsto t atTop (𝓝 0))
    (hf : Tendsto (fun j => f (u j) * t j ^ m) atTop (𝓝 α))
    (hg : Tendsto (fun j => g (u j) * t j ^ m) atTop (𝓝 β))
    (helim : GradedAlong (fun w => β * f w - α * g w) u t m' C') : m' < m := by
  obtain ⟨hC', hlim'⟩ := helim
  by_contra hlt
  have hle : m ≤ m' := not_lt.mp hlt
  have hzero := tendsto_leadingElimination hf hg
  have hpow : Tendsto (fun j => t j ^ (m' - m)) atTop (𝓝 (if m' = m then 1 else 0)) := by
    by_cases hm : m' = m
    · rw [if_pos hm, hm, Nat.sub_self]
      simp
    · rw [if_neg hm]
      have hp := ht.pow (m' - m)
      rwa [zero_pow (by omega)] at hp
  have hmul := hzero.mul hpow
  rw [zero_mul] at hmul
  refine hC' (tendsto_nhds_unique hlim' ?_)
  refine hmul.congr fun j => ?_
  rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]

/-- **Proportional leading values cancel.**  The elimination coefficients need not be the leading
values themselves: any pair proportional to them does. -/
theorem tendsto_leadingElimination_of_proportional {f g : ℂ → ℂ} {u t : ℕ → ℂ} {m : ℕ}
    {α β α' β' : ℂ} (hprop : β * α' = α * β')
    (hf : Tendsto (fun j => f (u j) * t j ^ m) atTop (𝓝 α'))
    (hg : Tendsto (fun j => g (u j) * t j ^ m) atTop (𝓝 β')) :
    Tendsto (fun j => (β * f (u j) - α * g (u j)) * t j ^ m) atTop (𝓝 0) := by
  have h := (hf.const_mul β).sub (hg.const_mul α)
  rw [show β * α' - α * β' = 0 by rw [hprop]; ring] at h
  refine h.congr fun j => ?_
  ring

/-- The proportional elimination also has strictly smaller order. -/
theorem order_lt_of_proportional_elimination {f g : ℂ → ℂ} {u t : ℕ → ℂ} {m m' : ℕ}
    {α β α' β' C' : ℂ} (ht : Tendsto t atTop (𝓝 0)) (hprop : β * α' = α * β')
    (hf : Tendsto (fun j => f (u j) * t j ^ m) atTop (𝓝 α'))
    (hg : Tendsto (fun j => g (u j) * t j ^ m) atTop (𝓝 β'))
    (helim : GradedAlong (fun w => β * f w - α * g w) u t m' C') : m' < m := by
  obtain ⟨hC', hlim'⟩ := helim
  by_contra hlt
  have hle : m ≤ m' := not_lt.mp hlt
  have hzero := tendsto_leadingElimination_of_proportional hprop hf hg
  have hpow : Tendsto (fun j => t j ^ (m' - m)) atTop (𝓝 (if m' = m then 1 else 0)) := by
    by_cases hm : m' = m
    · rw [if_pos hm, hm, Nat.sub_self]
      simp
    · rw [if_neg hm]
      have hp := ht.pow (m' - m)
      rwa [zero_pow (by omega)] at hp
  have hmul := hzero.mul hpow
  rw [zero_mul] at hmul
  refine hC' (tendsto_nhds_unique hlim' ?_)
  refine hmul.congr fun j => ?_
  rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]

/-! ## The elementary recombination -/

/-- The elementary matrix that replaces row `b` by the elimination against row `a`. -/
noncomputable def eliminationMatrix {N : ℕ} (a b : Fin N) (α β : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℂ) b
    ((-(1 / α)) • ((1 : Matrix (Fin N) (Fin N) ℂ) b + (-β) • (1 : Matrix (Fin N) (Fin N) ℂ) a))

/-- The elementary recombination is invertible for every shift. -/
theorem isUnit_det_eliminationMatrix {N : ℕ} {a b : Fin N} (hab : b ≠ a) {α β : ℂ} (hα : α ≠ 0) :
    IsUnit (eliminationMatrix a b α β).det := by
  rw [eliminationMatrix, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_add_smul_self _ hab, Matrix.det_one, mul_one]
  exact isUnit_iff_ne_zero.mpr (by simp [hα])


/-! ## A uniform valuation on the span -/

/-- Every nonzero combination of the family is graded, with an order and a leading value that do not
depend on the point of `Z`, along a chart shared by the whole span. -/
def UniformSpanValuation {N : ℕ} (S : Set ℂ) (M : Fin N → ℂ → ℂ) (Z : Set ℂ)
    (ord : (Fin N → ℂ) → ℕ) (lead : (Fin N → ℂ) → ℂ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ u t : ℕ → ℂ, (∀ j, u j ∈ S) ∧ Tendsto u atTop (𝓝 ζ) ∧
    Tendsto t atTop (𝓝 0) ∧
    ∀ c : Fin N → ℂ, c ≠ 0 →
      GradedAlong (fun w => ∑ a, c a * M a w) u t (ord c) (lead c)

theorem row_ne_zero_of_isUnit_det {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : IsUnit K.det)
    (a : Fin N) : K a ≠ 0 := by
  intro h
  refine (isUnit_iff_ne_zero.mp hK) ?_
  refine Matrix.det_eq_zero_of_row_eq_zero a fun j => ?_
  exact congrFun h j

/-- Every nonzero combination is graded, with an order independent of the point and a leading value
that factors as a per-order scale times a point-independent coefficient.  Only the *ratios inside an
order stratum* need to be independent of the point; the scale may vary freely, which is what a
Cauchy-type packet actually satisfies. -/
def StratifiedSpanValuation {N : ℕ} (S : Set ℂ) (M : Fin N → ℂ → ℂ) (Z : Set ℂ)
    (ord : (Fin N → ℂ) → ℕ) (γ : (Fin N → ℂ) → ℂ) (ρ : ℕ → ℂ → ℂ) : Prop :=
  Z.Infinite ∧ (∀ c : Fin N → ℂ, c ≠ 0 → γ c ≠ 0) ∧
    ∀ ζ ∈ Z, ∃ u t : ℕ → ℂ, (∀ j, u j ∈ S) ∧ Tendsto u atTop (𝓝 ζ) ∧
      Tendsto t atTop (𝓝 0) ∧ (∀ m : ℕ, ρ m ζ ≠ 0) ∧
      ∀ c : Fin N → ℂ, c ≠ 0 →
        GradedAlong (fun w => ∑ a, c a * M a w) u t (ord c) (ρ (ord c) ζ * γ c)

set_option maxHeartbeats 1000000 in
/-- **The search terminates.**  Repeated elimination of colliding orders reaches a recombination
whose orders are pairwise distinct: each step strictly lowers the total order, which cannot fall
below zero.  The elimination coefficients are the point-independent stratum coefficients. -/
theorem exists_injectiveOrder_recombination {N : ℕ} {S Z : Set ℂ} {M : Fin N → ℂ → ℂ}
    {ord : (Fin N → ℂ) → ℕ} {γ : (Fin N → ℂ) → ℂ} {ρ : ℕ → ℂ → ℂ}
    (hval : StratifiedSpanValuation S M Z ord γ ρ)
    (K : Matrix (Fin N) (Fin N) ℂ) (hK : IsUnit K.det) :
    ∃ K' : Matrix (Fin N) (Fin N) ℂ, IsUnit K'.det ∧
      Function.Injective (fun a => ord (K' a)) := by
  classical
  obtain ⟨hZ, hγ, hchart⟩ := hval
  obtain ⟨ζ, hζ⟩ := hZ.nonempty
  obtain ⟨u, t, humem, hu, ht, hρ, hgr⟩ := hchart ζ hζ
  have key : ∀ k : ℕ, ∀ L : Matrix (Fin N) (Fin N) ℂ, IsUnit L.det → (∑ a, ord (L a)) = k →
      ∃ K' : Matrix (Fin N) (Fin N) ℂ, IsUnit K'.det ∧
        Function.Injective (fun a => ord (K' a)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro L hL hsum
      by_cases hinj : Function.Injective (fun a => ord (L a))
      · exact ⟨L, hL, hinj⟩
      · obtain ⟨a₀, b₀, heq, hne⟩ := Function.not_injective_iff.mp hinj
        have hba : b₀ ≠ a₀ := fun h => hne h.symm
        have hrowA := row_ne_zero_of_isUnit_det hL a₀
        have hrowB := row_ne_zero_of_isUnit_det hL b₀
        obtain ⟨α, hαdef⟩ : ∃ x : ℂ, x = γ (L a₀) := ⟨_, rfl⟩
        obtain ⟨β, hβdef⟩ : ∃ x : ℂ, x = γ (L b₀) := ⟨_, rfl⟩
        have hα : α ≠ 0 := by rw [hαdef]; exact hγ (L a₀) hrowA
        have hgrA : GradedAlong (fun w => ∑ j, L a₀ j * M j w) u t
            (ord (L a₀)) (ρ (ord (L a₀)) ζ * α) := by
          rw [hαdef]; exact hgr (L a₀) hrowA
        have hgrB : GradedAlong (fun w => ∑ j, L b₀ j * M j w) u t
            (ord (L b₀)) (ρ (ord (L b₀)) ζ * β) := by
          rw [hβdef]; exact hgr (L b₀) hrowB
        obtain ⟨c, hc⟩ : ∃ v : Fin N → ℂ, v = fun j => β * L a₀ j - α * L b₀ j := ⟨_, rfl⟩
        have hcne : c ≠ 0 := by
          intro h0
          refine (isUnit_iff_ne_zero.mp hL) ?_
          have hrow0 : ∀ j, α * L b₀ j = β * L a₀ j := by
            intro j
            have hj := congrFun h0 j
            rw [hc] at hj
            simp only [Pi.zero_apply] at hj
            linear_combination -hj
          have hrow : L b₀ = (β / α) • L a₀ := by
            funext j
            simp only [Pi.smul_apply, smul_eq_mul]
            field_simp
            linear_combination hrow0 j
          have hz : Matrix.updateRow L b₀ (L b₀ + (-(β / α)) • L a₀) = Matrix.updateRow L b₀ 0 := by
            rw [hrow]
            congr 1
            funext j
            simp
          have h1 := Matrix.det_updateRow_add_smul_self L hba (-(β / α))
          rw [hz] at h1
          rw [← h1]
          exact Matrix.det_eq_zero_of_row_eq_zero b₀ fun j => by simp
        have hcomb : ∀ w : ℂ, (∑ j, c j * M j w)
            = β * (∑ j, L a₀ j * M j w) - α * (∑ j, L b₀ j * M j w) := by
          intro w
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by rw [hc]; ring
        have hclt : ord c < ord (L a₀) := by
          have hgc := hgr c hcne
          have hfun : (fun w => ∑ j, c j * M j w)
              = fun w => β * (∑ j, L a₀ j * M j w) - α * (∑ j, L b₀ j * M j w) :=
            funext hcomb
          have hgc' : GradedAlong
              (fun w => β * (∑ j, L a₀ j * M j w) - α * (∑ j, L b₀ j * M j w)) u t
              (ord c) (ρ (ord c) ζ * γ c) := by
            rw [← hfun]
            exact hgc
          have hb := hgrB.2
          rw [show ord (L b₀) = ord (L a₀) from heq.symm] at hb
          refine order_lt_of_proportional_elimination
            (f := fun w => ∑ j, L a₀ j * M j w) (g := fun w => ∑ j, L b₀ j * M j w)
            (u := u) (t := t) (m := ord (L a₀)) (m' := ord c) (α := α) (β := β)
            (α' := ρ (ord (L a₀)) ζ * α) (β' := ρ (ord (L a₀)) ζ * β)
            (C' := ρ (ord c) ζ * γ c) ht ?_ hgrA.2 hb hgc'
          ring
        obtain ⟨L', hL'⟩ : ∃ X : Matrix (Fin N) (Fin N) ℂ, X = Matrix.updateRow L b₀ c := ⟨_, rfl⟩
        have hrows : ∀ a, a ≠ b₀ → L' a = L a := by
          intro a ha
          rw [hL']
          exact Matrix.updateRow_ne ha
        have hLb : L' b₀ = c := by rw [hL']; exact Matrix.updateRow_self
        have hL'unit : IsUnit L'.det := by
          have hsmul : c = (-α) • (L b₀ + (-(β / α)) • L a₀) := by
            funext j
            rw [hc]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            field_simp
            ring
          rw [hL', hsmul, Matrix.det_updateRow_smul,
            Matrix.det_updateRow_add_smul_self L hba (-(β / α))]
          exact (isUnit_iff_ne_zero.mpr (by simp [hα])).mul hL
        have hless : (∑ a, ord (L' a)) < ∑ a, ord (L a) := by
          refine Finset.sum_lt_sum (fun a _ => ?_) ⟨b₀, Finset.mem_univ b₀, ?_⟩
          · by_cases ha : a = b₀
            · subst ha
              rw [hLb]
              exact le_of_lt (heq ▸ hclt)
            · rw [hrows a ha]
          · rw [hLb, ← heq]
            exact hclt
        exact IH _ (by omega) L' hL'unit rfl
  exact key (∑ a, ord (K a)) K hK rfl

/-! ## The closure -/

/-- Any invertible recombination of a stratified family is graded. -/
theorem gradedBlowUpFamily_of_stratifiedSpanValuation {N : ℕ} {S Z : Set ℂ} {M : Fin N → ℂ → ℂ}
    {ord : (Fin N → ℂ) → ℕ} {γ : (Fin N → ℂ) → ℂ} {ρ : ℕ → ℂ → ℂ}
    (hval : StratifiedSpanValuation S M Z ord γ ρ)
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : IsUnit K.det) :
    GradedBlowUpFamily S (fun a w => ∑ b, K a b * M b w) Z (fun a => ord (K a)) := by
  obtain ⟨hZ, hγ, hchart⟩ := hval
  refine ⟨hZ, ?_⟩
  intro ζ hζ
  obtain ⟨u, t, humem, hu, ht, hρ, hgr⟩ := hchart ζ hζ
  exact ⟨u, t, fun a => ρ (ord (K a)) ζ * γ (K a), humem, hu, ht,
    fun a => (hgr (K a) (row_ne_zero_of_isUnit_det hK a)).1,
    fun a => (hgr (K a) (row_ne_zero_of_isUnit_det hK a)).2⟩

/-- **A stratified valuation on the span decides the degree box.**  The elimination search
terminates at a recombination with pairwise distinct orders, the graded law decides that box, and
the recombination transports the verdict back. -/
theorem linearIndependent_degreeBox_of_stratifiedSpanValuation {N q : ℕ} {S Z : Set ℂ}
    {M : Fin N → ℂ → ℂ} {ord : (Fin N → ℂ) → ℕ} {γ : (Fin N → ℂ) → ℂ} {ρ : ℕ → ℂ → ℂ}
    (hval : StratifiedSpanValuation S M Z ord γ ρ) :
    LinearIndependent ℂ
      (fun p : Fin N × Fin (q + 1) => Set.restrict S (fun w => w ^ (p.2 : ℕ) * M p.1 w)) := by
  obtain ⟨K, hK, hinj⟩ := exists_injectiveOrder_recombination hval 1
    (by rw [Matrix.det_one]; exact isUnit_one)
  have hgraded := gradedBlowUpFamily_of_stratifiedSpanValuation hval hK
  have hbox := linearIndependent_restrict_degreeBox_of_gradedBlowUp (q := q) hgraded hinj
  refine linearIndependent_of_blockComb (Matrix.isUnit_nonsing_inv_det K hK) ?_ hbox
  intro a i
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.restrict_apply]
  have hmul : ∀ w : ℂ, ∑ b, K⁻¹ a b * (∑ c, K b c * M c w) = M a w := by
    intro w
    have hexp : ∑ b, K⁻¹ a b * (∑ c, K b c * M c w)
        = ∑ c, (∑ b, K⁻¹ a b * K b c) * M c w := by
      have h1 : ∀ b, K⁻¹ a b * (∑ c, K b c * M c w)
          = ∑ c, (K⁻¹ a b * K b c) * M c w := by
        intro b
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]
    rw [hexp]
    have hid : ∀ c, (∑ b, K⁻¹ a b * K b c) = if a = c then 1 else 0 := by
      intro c
      have := congrFun (congrFun (Matrix.nonsing_inv_mul K hK) a) c
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    simp only [hid, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  calc (x : ℂ) ^ (i : ℕ) * M a (x : ℂ)
      = (x : ℂ) ^ (i : ℕ) * ∑ b, K⁻¹ a b * (∑ c, K b c * M c (x : ℂ)) := by rw [hmul]
    _ = ∑ b, K⁻¹ a b * ((x : ℂ) ^ (i : ℕ) * ∑ c, K b c * M c (x : ℂ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

/-- A uniform valuation is the stratified one with trivial scale. -/
theorem stratifiedSpanValuation_of_uniform {N : ℕ} {S Z : Set ℂ} {M : Fin N → ℂ → ℂ}
    {ord : (Fin N → ℂ) → ℕ} {lead : (Fin N → ℂ) → ℂ}
    (hval : UniformSpanValuation S M Z ord lead) :
    StratifiedSpanValuation S M Z ord lead (fun _ _ => 1) := by
  obtain ⟨hZ, hchart⟩ := hval
  obtain ⟨ζ₀, hζ₀⟩ := hZ.nonempty
  obtain ⟨u₀, t₀, humem₀, hu₀, ht₀, hgr₀⟩ := hchart ζ₀ hζ₀
  refine ⟨hZ, fun c hc => (hgr₀ c hc).1, ?_⟩
  intro ζ hζ
  obtain ⟨u, t, humem, hu, ht, hgr⟩ := hchart ζ hζ
  refine ⟨u, t, humem, hu, ht, fun m => one_ne_zero, ?_⟩
  intro c hc
  rw [one_mul]
  exact hgr c hc

/-- **A uniform valuation on the span decides the degree box.** -/
theorem linearIndependent_degreeBox_of_uniformSpanValuation {N q : ℕ} {S Z : Set ℂ}
    {M : Fin N → ℂ → ℂ} {ord : (Fin N → ℂ) → ℕ} {lead : (Fin N → ℂ) → ℂ}
    (hval : UniformSpanValuation S M Z ord lead) :
    LinearIndependent ℂ
      (fun p : Fin N × Fin (q + 1) => Set.restrict S (fun w => w ^ (p.2 : ℕ) * M p.1 w)) :=
  linearIndependent_degreeBox_of_stratifiedSpanValuation (stratifiedSpanValuation_of_uniform hval)

/-- **The uniform valuation is realized.**  The pole model is exactly the reciprocal of the scale, so
every nonzero multiple is graded at order one with its own coefficient as leading value — and both
data are independent of the point. -/
theorem uniformSpanValuation_periodicPoleModel :
    UniformSpanValuation upperHalfPlane ![periodicPoleModel] (Set.range fun m : ℤ => (m : ℂ))
      (fun _ => 1) (fun c => c 0) := by
  refine ⟨Set.infinite_range_of_injective (fun x y h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨m, rfl⟩
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach m
  refine ⟨u, fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1,
    humem, hlim, hexp, ?_⟩
  intro c hc
  have hc0 : c 0 ≠ 0 := by
    intro h
    refine hc (funext fun j => ?_)
    fin_cases j
    exact h
  refine ⟨hc0, ?_⟩
  have hval : ∀ j, (∑ a : Fin 1, c a * (![periodicPoleModel] a) (u j)) *
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (1 : ℕ) = c 0 := by
    intro j
    rw [Fin.sum_univ_one, pow_one]
    show c 0 * periodicPoleModel (u j) *
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) = c 0
    rw [mul_assoc, periodicPoleModel, inv_mul_cancel₀ (hne j), mul_one]
  exact tendsto_const_nhds.congr fun j => (hval j).symm

end GaloisForLFunctions.HTGeometry
