import GaloisForLFunctions.InfiniteRankPurityTheory.ASchurFunctionReducesAtEveryNode
import GaloisForLFunctions.InfiniteRankPurityTheory.TheIndexBoundIsAttained
import GaloisForLFunctions.InfiniteRankPurityTheory.TheLineLawSeesTheStripAndNotTheLine
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw

/-!
# A defect of degree `κ` has at most `κ` exceptional points

The index law at any index. A finite Blaschke product of degree `≤ κ` on the half-plane
`Re s > ½` is a quotient `B = N / (ε N^*)`, where `N` is a polynomial of degree `≤ κ`,
`N^*(s) = conj (N(1 − s̄))` is its reflection in the line, `‖ε‖ = 1`, and `N^* ≠ 0`, `‖N‖ ≤ ‖N^*‖`
on the half-plane (`IsBlaschke`). Products `c · Π b_w` of `κ` defect factors are of this form
(`isBlaschke_prod`).

**Theorem** (`eqOn_of_card_agreements`, `encard_agreements_le`). A Schur function `θ` on the
half-plane that agrees with a Blaschke product `B` of degree `≤ κ` at `κ + 1` points equals it. If
`θ ≠ B` somewhere, the equation `θ = B` has at most `κ` solutions in the half-plane.

**Proof.** Induction on `κ` by the Schur reduction at an agreement `s₀`. If `‖B(s₀)‖ = 1` both
functions are constant. Otherwise `M_v ∘ θ = φ · b_{s₀}` with `φ` a Schur function, `v = B(s₀)`, and
`M_v ∘ B = B' · b_{s₀}` with `B'` a Blaschke product of degree `≤ κ − 1` (`IsBlaschke.reduce`): with
`D = ε N^*` the numerator `N − v D` vanishes at `s₀`, so `N − v D = (X − s₀) N₁`, and reflecting this
identity gives `D − v̄ N = −ε (X − (1 − s̄₀)) N₁^*`. No factorization into roots is used. The other
agreements persist, so `φ = B'` and `θ = B`.

**Consequences.**
* `hermiteBiehler_index`: a Hermite–Biehler sum `P_W E − c P_{W♯} E'` with `E ≠ 0`, `‖E'‖ ≤ ‖E‖`
  right of the line and a defect `P_W` of degree `κ` has at most `κ` zeros right of the line.
* `hermiteBiehler_index_general`, `pencil_index_general`: for a defect with zeros on both sides of
  the line the index is the number of its zeros right of the line; zeros left of the line cost
  nothing. Over any fixed part with zeros in the closed strip, the family with such a defect has
  that index at every height `Y ≥ 1`.
* `hermiteBiehler_indexZero`, `halfShift_ne_zero`, `re_eq_half_of_xi_halfShift_eq_zero`: at index
  zero there is no zero off the line at all. Over any fixed part with zeros in the closed strip the
  half-shifts `G(s + ½) ± G(s − ½)` are pure; for `G = ξ` this is Taylor's theorem.
* `two_mul_encard_upper_zeros_le`: with real data at most `κ/2` of them lie above the real axis:
  the parity law at index `κ`. At `κ = 1` it is purity off the real axis.
* `index_attained`: for every finite configuration `W` right of the line the `cosh` model
  `P_W P_{W♯} (e^{s−½} + e^{½−s})` is such a sum and vanishes right of the line exactly on `W`. The
  bound is attained at every index by every configuration.
-/

open Complex Set Metric Filter Topology Polynomial

namespace GaloisForLFunctions.InfiniteRankPurityTheory

noncomputable section

/-! ### The reflection of a polynomial -/

theorem conj_eval (P : ℂ[X]) (y : ℂ) :
    (starRingEnd ℂ) (P.eval y) = (P.map (starRingEnd ℂ)).eval ((starRingEnd ℂ) y) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [eval_add, map_add, Polynomial.map_add, eval_add, hp, hq]
  | monomial n a => rw [eval_monomial, Polynomial.map_monomial, eval_monomial, map_mul, map_pow]

/-- `P^*(s) = conj (P(1 − s̄))`, the reflection of `P` in the line `Re s = ½`. -/
def pstar (P : ℂ[X]) : ℂ[X] := (P.map (starRingEnd ℂ)).comp (1 - X)

theorem pstar_eval (P : ℂ[X]) (s : ℂ) :
    (pstar P).eval s = (starRingEnd ℂ) (P.eval (1 - (starRingEnd ℂ) s)) := by
  rw [conj_eval, pstar, eval_comp, eval_sub, eval_one, eval_X, map_sub, map_one,
    Complex.conj_conj]

theorem pstar_pstar (P : ℂ[X]) : pstar (pstar P) = P := by
  refine Polynomial.funext fun s => ?_
  rw [pstar_eval, pstar_eval]
  simp

theorem pstar_sub_C_mul (P Q : ℂ[X]) (a : ℂ) :
    pstar (P - C a * Q) = pstar P - C ((starRingEnd ℂ) a) * pstar Q := by
  refine Polynomial.funext fun s => ?_
  simp only [pstar_eval, eval_sub, eval_mul, eval_C, map_sub, map_mul]

theorem pstar_C_mul (a : ℂ) (Q : ℂ[X]) : pstar (C a * Q) = C ((starRingEnd ℂ) a) * pstar Q := by
  refine Polynomial.funext fun s => ?_
  simp only [pstar_eval, eval_mul, eval_C, map_mul]

/-- Reflection turns the factor `X − a` into `−(X − (1 − ā))`. -/
theorem pstar_X_sub_C_mul (a : ℂ) (Q : ℂ[X]) :
    pstar ((X - C a) * Q) = -((X - C (1 - (starRingEnd ℂ) a)) * pstar Q) := by
  refine Polynomial.funext fun s => ?_
  simp only [pstar_eval, eval_mul, eval_sub, eval_X, eval_C, eval_neg, eval_one, map_mul, map_sub,
    map_one, Complex.conj_conj]
  ring

theorem natDegree_pstar_le (P : ℂ[X]) : (pstar P).natDegree ≤ P.natDegree := by
  have h1 : (1 - X : ℂ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    simp
  calc (pstar P).natDegree
      ≤ (P.map (starRingEnd ℂ)).natDegree * (1 - X : ℂ[X]).natDegree := natDegree_comp_le
    _ ≤ (P.map (starRingEnd ℂ)).natDegree * 1 := Nat.mul_le_mul_left _ h1
    _ ≤ P.natDegree := by
        rw [mul_one]
        exact natDegree_map_le

/-! ### Finite Blaschke products on the half-plane -/

/-- `B` is on the half-plane a finite Blaschke product of degree at most `κ`: `B = N / (ε N^*)`
with a polynomial `N` of degree `≤ κ`, `‖ε‖ = 1`, and `N^* ≠ 0`, `‖N‖ ≤ ‖N^*‖` on the
half-plane. -/
def IsBlaschke (κ : ℕ) (B : ℂ → ℂ) : Prop :=
  ∃ (N : ℂ[X]) (ε : ℂ), N.natDegree ≤ κ ∧ ‖ε‖ = 1 ∧ (∀ s ∈ rightHalf, (pstar N).eval s ≠ 0) ∧
    (∀ s ∈ rightHalf, ‖N.eval s‖ ≤ ‖(pstar N).eval s‖) ∧
    ∀ s ∈ rightHalf, B s = N.eval s / (ε * (pstar N).eval s)

theorem ne_zero_of_norm_eq_one {ε : ℂ} (hε : ‖ε‖ = 1) : ε ≠ 0 := fun h => by
  rw [h, norm_zero] at hε
  exact zero_ne_one hε

theorem IsBlaschke.differentiableOn {κ : ℕ} {B : ℂ → ℂ} (hB : IsBlaschke κ B) :
    DifferentiableOn ℂ B rightHalf := by
  obtain ⟨N, ε, -, hε, hne, -, hBeq⟩ := hB
  have hε0 := ne_zero_of_norm_eq_one hε
  have hd : DifferentiableOn ℂ (fun s => N.eval s / (ε * (pstar N).eval s)) rightHalf := by
    intro s hs
    exact (N.differentiable.differentiableAt.div
      ((differentiableAt_const _).mul (pstar N).differentiable.differentiableAt)
      (mul_ne_zero hε0 (hne s hs))).differentiableWithinAt
  exact hd.congr hBeq

theorem IsBlaschke.norm_le_one {κ : ℕ} {B : ℂ → ℂ} (hB : IsBlaschke κ B) {s : ℂ}
    (hs : s ∈ rightHalf) : ‖B s‖ ≤ 1 := by
  obtain ⟨N, ε, -, hε, -, hle, hBeq⟩ := hB
  rw [hBeq s hs, norm_div, norm_mul, hε, one_mul]
  exact div_le_one_of_le₀ (hle s hs) (norm_nonneg _)

/-- A Blaschke product of degree zero is a unimodular constant. -/
theorem IsBlaschke.norm_eq_one_of_zero {B : ℂ → ℂ} (hB : IsBlaschke 0 B) {s : ℂ}
    (hs : s ∈ rightHalf) : ‖B s‖ = 1 := by
  obtain ⟨N, ε, hN, hε, hne, -, hBeq⟩ := hB
  obtain ⟨a, rfl⟩ : ∃ a : ℂ, N = C a := ⟨_, eq_C_of_natDegree_le_zero hN⟩
  have h2 : (pstar (C a)).eval s = (starRingEnd ℂ) a := by rw [pstar_eval, eval_C]
  have hne' := hne s hs
  rw [h2] at hne'
  have ha : a ≠ 0 := fun h => hne' (by rw [h, map_zero])
  rw [hBeq s hs, h2, eval_C, norm_div, norm_mul, hε, one_mul, RCLike.norm_conj,
    div_self (norm_ne_zero_iff.mpr ha)]

/-- **One step of the Schur algorithm lowers the degree.** If `B` is a Blaschke product of degree
`≤ κ + 1` and `‖B(s₀)‖ < 1`, then `M_{B(s₀)} ∘ B = B' · b_{s₀}` with `B'` a Blaschke product of
degree `≤ κ`. -/
theorem IsBlaschke.reduce {κ : ℕ} {B : ℂ → ℂ} (hB : IsBlaschke (κ + 1) B) {s₀ : ℂ}
    (hs₀ : s₀ ∈ rightHalf) (hv : ‖B s₀‖ < 1) :
    ∃ B' : ℂ → ℂ, IsBlaschke κ B' ∧
      ∀ s ∈ rightHalf, B' s * defectFactor s₀ s = mobius (B s₀) (B s) := by
  have hBd := hB.differentiableOn
  have hBb : ∀ s ∈ rightHalf, ‖B s‖ ≤ 1 := fun s hs => hB.norm_le_one hs
  obtain ⟨N, ε, hN, hε, hne, hle, hBeq⟩ := hB
  have hε0 := ne_zero_of_norm_eq_one hε
  have hεε : ε * (starRingEnd ℂ) ε = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hε]
    norm_num
  -- the numerator `N' = N − v D`, `D = ε N^*`, vanishes at the node
  obtain ⟨N', hN'⟩ : ∃ N' : ℂ[X], N' = N - C (B s₀) * (C ε * pstar N) := ⟨_, rfl⟩
  have hN'eval : ∀ s, N'.eval s = N.eval s - B s₀ * (ε * (pstar N).eval s) := by
    intro s
    rw [hN']
    simp only [eval_sub, eval_mul, eval_C]
  have hroot : N'.IsRoot s₀ := by
    have hD : ε * (pstar N).eval s₀ ≠ 0 := mul_ne_zero hε0 (hne s₀ hs₀)
    rw [IsRoot.def, hN'eval, hBeq s₀ hs₀, div_mul_cancel₀ _ hD, sub_self]
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℂ[X], N₁ = N' /ₘ (X - C s₀) := ⟨_, rfl⟩
  have hfac : (X - C s₀) * N₁ = N' := by
    rw [hN₁]
    exact mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hdeg : N₁.natDegree ≤ κ := by
    have h1 : N'.natDegree ≤ κ + 1 := by
      rw [hN']
      exact (natDegree_sub_le _ _).trans (max_le hN ((natDegree_C_mul_le _ _).trans
        ((natDegree_C_mul_le _ _).trans ((natDegree_pstar_le N).trans hN))))
    rw [hN₁, natDegree_divByMonic _ (monic_X_sub_C s₀), natDegree_X_sub_C]
    omega
  -- reflecting `N' = (X − s₀) N₁` gives the denominator
  have hstar : ∀ s, -((s - (1 - (starRingEnd ℂ) s₀)) * (pstar N₁).eval s) =
      (pstar N).eval s - (starRingEnd ℂ) (B s₀) * ((starRingEnd ℂ) ε * N.eval s) := by
    intro s
    have h1 : pstar N' =
        pstar N - C ((starRingEnd ℂ) (B s₀)) * (C ((starRingEnd ℂ) ε) * N) := by
      rw [hN', pstar_sub_C_mul, pstar_C_mul, pstar_pstar]
    have h2 : pstar N' = -((X - C (1 - (starRingEnd ℂ) s₀)) * pstar N₁) := by
      rw [← hfac, pstar_X_sub_C_mul]
    have h3 := congrArg (fun P : ℂ[X] => P.eval s) (h2.symm.trans h1)
    simpa only [eval_neg, eval_mul, eval_sub, eval_X, eval_C] using h3
  have hrel : ∀ s, ε * (pstar N).eval s - (starRingEnd ℂ) (B s₀) * N.eval s =
      -ε * ((s - (1 - (starRingEnd ℂ) s₀)) * (pstar N₁).eval s) := by
    intro s
    linear_combination (-ε) * hstar s + ((starRingEnd ℂ) (B s₀) * N.eval s) * hεε
  have hden : ∀ s ∈ rightHalf,
      ε * (pstar N).eval s - (starRingEnd ℂ) (B s₀) * N.eval s ≠ 0 := by
    intro s hs h0
    have h1 : ε * (pstar N).eval s = (starRingEnd ℂ) (B s₀) * N.eval s := sub_eq_zero.mp h0
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, hε, one_mul, RCLike.norm_conj] at h2
    have h3 : 0 < ‖(pstar N).eval s‖ := norm_pos_iff.mpr (hne s hs)
    have h4 : ‖B s₀‖ * ‖N.eval s‖ ≤ ‖B s₀‖ * ‖(pstar N).eval s‖ :=
      mul_le_mul_of_nonneg_left (hle s hs) (norm_nonneg _)
    nlinarith
  have hN₁ne : ∀ s ∈ rightHalf, (pstar N₁).eval s ≠ 0 := by
    intro s hs h0
    apply hden s hs
    rw [hrel s, h0]
    ring
  have hred : ∀ s ∈ rightHalf,
      N₁.eval s / (-ε * (pstar N₁).eval s) * defectFactor s₀ s = mobius (B s₀) (B s) := by
    intro s hs
    have hD : ε * (pstar N).eval s ≠ 0 := mul_ne_zero hε0 (hne s hs)
    have hD2 := defect_denom_ne_zero hs₀ hs
    have hM1 := hN₁ne s hs
    have e1 : N.eval s / (ε * (pstar N).eval s) - B s₀ =
        (N.eval s - B s₀ * (ε * (pstar N).eval s)) / (ε * (pstar N).eval s) := by
      rw [sub_div, mul_div_cancel_right₀ _ hD]
    have e2 : 1 - (starRingEnd ℂ) (B s₀) * (N.eval s / (ε * (pstar N).eval s)) =
        (ε * (pstar N).eval s - (starRingEnd ℂ) (B s₀) * N.eval s) / (ε * (pstar N).eval s) := by
      rw [sub_div, div_self hD, mul_div_assoc]
    have hN'fac : N'.eval s = (s - s₀) * N₁.eval s := by
      rw [← hfac]
      simp only [eval_mul, eval_sub, eval_X, eval_C]
    rw [mobius, hBeq s hs, e1, e2, div_div_div_cancel_right₀ hD, ← hN'eval, hrel s, hN'fac,
      defectFactor]
    field_simp
  refine ⟨fun s => N₁.eval s / (-ε * (pstar N₁).eval s),
    ⟨N₁, -ε, hdeg, by rw [norm_neg, hε], hN₁ne, ?_, fun s _ => rfl⟩, hred⟩
  -- the Schur bound of the quotient: off the node by the Schwarz lemma, at the node by continuity
  have hoff : ∀ s ∈ rightHalf, s ≠ s₀ → ‖N₁.eval s‖ ≤ ‖(pstar N₁).eval s‖ := by
    intro s hs hne'
    have hb0 := defectFactor_ne_zero hs₀ hs hne'
    have hsw := norm_le_norm_defectFactor (differentiableOn_mobius_comp hBd hBb hv)
      (fun z hz => norm_mobius_le hv (hBb z hz)) hs₀ (mobius_self _) hs
    rw [← hred s hs, norm_mul] at hsw
    have h1 : ‖N₁.eval s / (-ε * (pstar N₁).eval s)‖ ≤ 1 :=
      le_of_mul_le_mul_right (by rwa [one_mul]) (norm_pos_iff.mpr hb0)
    rw [norm_div, norm_mul, norm_neg, hε, one_mul,
      div_le_one (norm_pos_iff.mpr (hN₁ne s hs))] at h1
    exact h1
  intro s hs
  by_cases hne' : s = s₀
  · subst hne'
    have hc1 : Tendsto (fun z => ‖N₁.eval z‖) (𝓝[≠] s) (𝓝 ‖N₁.eval s‖) :=
      (N₁.continuous.norm.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have hc2 : Tendsto (fun z => ‖(pstar N₁).eval z‖) (𝓝[≠] s) (𝓝 ‖(pstar N₁).eval s‖) :=
      ((pstar N₁).continuous.norm.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hc1 hc2 ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_rightHalf.mem_nhds hs)] with z hz hzr
    exact hoff z hzr hz
  · exact hoff s hs hne'

/-! ### The index law -/

/-- **Agreement at `κ + 1` points forces identity.** A Schur function on the half-plane that
agrees with a Blaschke product of degree `≤ κ` at more than `κ` points equals it. -/
theorem eqOn_of_card_agreements : ∀ (κ : ℕ) {θ B : ℂ → ℂ}, DifferentiableOn ℂ θ rightHalf →
    (∀ s ∈ rightHalf, ‖θ s‖ ≤ 1) → IsBlaschke κ B → ∀ S : Finset ℂ, κ < S.card →
    (∀ s ∈ S, s ∈ rightHalf ∧ θ s = B s) → EqOn θ B rightHalf := by
  intro κ
  induction κ with
  | zero =>
    intro θ B hθ hb hB S hS hag
    obtain ⟨s₀, hs₀S⟩ := Finset.card_pos.mp hS
    obtain ⟨hs₀, e₀⟩ := hag s₀ hs₀S
    have h1B : ‖B s₀‖ = 1 := hB.norm_eq_one_of_zero hs₀
    have h1 : ‖θ s₀‖ = 1 := by rw [e₀]; exact h1B
    intro s hs
    rw [eqOn_const_of_norm_eq_one hθ hb hs₀ h1 hs,
      eqOn_const_of_norm_eq_one hB.differentiableOn (fun z hz => hB.norm_le_one hz) hs₀ h1B hs, e₀]
  | succ κ ih =>
    intro θ B hθ hb hB S hS hag
    obtain ⟨s₀, hs₀S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    obtain ⟨hs₀, e₀⟩ := hag s₀ hs₀S
    have hBb : ∀ z ∈ rightHalf, ‖B z‖ ≤ 1 := fun z hz => hB.norm_le_one hz
    rcases (hBb s₀ hs₀).lt_or_eq with hv | hv
    · -- reduce both functions at the node `s₀`
      obtain ⟨φ, hφd, hφb, hφ⟩ := exists_schur_reduction hθ hb hs₀ (by rw [e₀]; exact hv)
      obtain ⟨B', hB', hB'red⟩ := hB.reduce hs₀ hv
      have hcard : κ < (S.erase s₀).card := by
        rw [Finset.card_erase_of_mem hs₀S]
        omega
      have hag' : ∀ s ∈ S.erase s₀, s ∈ rightHalf ∧ φ s = B' s := by
        intro s hs
        obtain ⟨hne, hsS⟩ := Finset.mem_erase.mp hs
        obtain ⟨hsr, es⟩ := hag s hsS
        refine ⟨hsr, ?_⟩
        have h1 := hφ s hsr
        rw [e₀, es, ← hB'red s hsr] at h1
        exact mul_right_cancel₀ (defectFactor_ne_zero hs₀ hsr hne) h1
      have heq := ih hφd hφb hB' (S.erase s₀) hcard hag'
      intro s hs
      have h1 := hφ s hs
      rw [heq hs, hB'red s hs, e₀] at h1
      exact mobius_injOn hv (hb s hs) (hBb s hs) h1.symm
    · -- both functions are constant
      have h1 : ‖θ s₀‖ = 1 := by rw [e₀]; exact hv
      intro s hs
      rw [eqOn_const_of_norm_eq_one hθ hb hs₀ h1 hs,
        eqOn_const_of_norm_eq_one hB.differentiableOn hBb hs₀ hv hs, e₀]

/-- **At most `κ` exceptional points.** If the Schur function `θ` differs somewhere from the
Blaschke product `B` of degree `≤ κ`, the equation `θ = B` has at most `κ` solutions in the
half-plane. -/
theorem encard_agreements_le {κ : ℕ} {θ B : ℂ → ℂ} (hθ : DifferentiableOn ℂ θ rightHalf)
    (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1) (hB : IsBlaschke κ B)
    (hdiff : ∃ z ∈ rightHalf, θ z ≠ B z) :
    {s | s ∈ rightHalf ∧ θ s = B s}.encard ≤ κ := by
  by_contra hcon
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.mp hcon))
  have hTcard' : T.encard = ((κ + 1 : ℕ) : ℕ∞) := by
    rw [hTcard]
    push_cast
    rfl
  have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard'
  have hcard : κ < hTfin.toFinset.card := by
    have h := hTfin.encard_eq_coe_toFinset_card
    rw [hTcard'] at h
    have h' : κ + 1 = hTfin.toFinset.card := by exact_mod_cast h
    omega
  obtain ⟨z, hz, hne⟩ := hdiff
  exact hne (eqOn_of_card_agreements κ hθ hb hB hTfin.toFinset hcard
    (fun s hs => hTsub (hTfin.mem_toFinset.mp hs)) hz)

/-! ### Products of defect factors -/

theorem isBlaschke_const {c : ℂ} (hc : ‖c‖ = 1) : IsBlaschke 0 fun _ => c := by
  have hc0 := ne_zero_of_norm_eq_one hc
  refine ⟨C 1, c⁻¹, by simp, by rw [norm_inv, hc, inv_one], fun s _ => ?_, fun s _ => ?_,
    fun s _ => ?_⟩
  · rw [pstar_eval]
    simp
  · rw [pstar_eval]
    simp
  · rw [pstar_eval]
    simp

/-- Multiplying by a defect factor raises the degree by one. -/
theorem IsBlaschke.defectFactor_mul {κ : ℕ} {B : ℂ → ℂ} (hB : IsBlaschke κ B) {w : ℂ}
    (hw : w ∈ rightHalf) : IsBlaschke (κ + 1) fun s => defectFactor w s * B s := by
  obtain ⟨N, ε, hN, hε, hne, hle, hBeq⟩ := hB
  have hε0 := ne_zero_of_norm_eq_one hε
  have hev : ∀ s, (pstar ((X - C w) * N)).eval s =
      -((s - (1 - (starRingEnd ℂ) w)) * (pstar N).eval s) := by
    intro s
    rw [pstar_X_sub_C_mul]
    simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C]
  refine ⟨(X - C w) * N, -ε, ?_, by rw [norm_neg, hε], fun s hs => ?_, fun s hs => ?_,
    fun s hs => ?_⟩
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_X_sub_C]
    omega
  · rw [hev]
    exact neg_ne_zero.mpr (mul_ne_zero (defect_denom_ne_zero hw hs) (hne s hs))
  · rw [hev, norm_neg, norm_mul]
    simp only [eval_mul, eval_sub, eval_X, eval_C, norm_mul]
    exact mul_le_mul (norm_sub_le_norm_sub_reflect hw hs) (hle s hs) (norm_nonneg _)
      (norm_nonneg _)
  · have hD := defect_denom_ne_zero hw hs
    have hN0 := hne s hs
    show defectFactor w s * B s =
      ((X - C w) * N).eval s / (-ε * (pstar ((X - C w) * N)).eval s)
    rw [hev, hBeq s hs, defectFactor]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    field_simp

/-- **A product of `κ` defect factors is a Blaschke product of degree `≤ κ`.** -/
theorem isBlaschke_prod {c : ℂ} (hc : ‖c‖ = 1) (W : Multiset ℂ) (hW : ∀ w ∈ W, w ∈ rightHalf) :
    IsBlaschke (Multiset.card W) fun s => c * (W.map fun w => defectFactor w s).prod := by
  induction W using Multiset.induction_on with
  | empty => simpa using isBlaschke_const hc
  | cons w W ih =>
    have h1 := (ih fun z hz => hW z (Multiset.mem_cons_of_mem hz)).defectFactor_mul
      (hW w (Multiset.mem_cons_self w W))
    have hfun : (fun s => c * ((w ::ₘ W).map fun w => defectFactor w s).prod) =
        fun s => defectFactor w s * (c * (W.map fun w => defectFactor w s).prod) := by
      funext s
      rw [Multiset.map_cons, Multiset.prod_cons]
      ring
    rw [Multiset.card_cons, hfun]
    exact h1

/-! ### Hermite–Biehler sums with a defect of degree `κ` -/

/-- The reflected divisor `W♯ = {1 − w̄ : w ∈ W}`. -/
def reflectDivisor (W : Multiset ℂ) : Multiset ℂ := W.map fun w => 1 - (starRingEnd ℂ) w

theorem divisorPoly_reflect (W : Multiset ℂ) (s : ℂ) :
    divisorPoly (reflectDivisor W) s = (W.map fun w => s - (1 - (starRingEnd ℂ) w)).prod := by
  rw [divisorPoly, reflectDivisor, Multiset.map_map]
  rfl

theorem divisorPoly_reflect_ne_zero {W : Multiset ℂ} (hW : ∀ w ∈ W, w ∈ rightHalf) {s : ℂ}
    (hs : s ∈ rightHalf) : divisorPoly (reflectDivisor W) s ≠ 0 := by
  rw [Ne, divisorPoly_eq_zero_iff, reflectDivisor, Multiset.mem_map]
  rintro ⟨w, hw, hsw⟩
  exact defect_denom_ne_zero (hW w hw) hs (by rw [hsw, sub_self])

theorem prod_defectFactor (W : Multiset ℂ) (s : ℂ) :
    (W.map fun w => defectFactor w s).prod =
      divisorPoly W s / divisorPoly (reflectDivisor W) s := by
  rw [divisorPoly_reflect, divisorPoly, ← Multiset.prod_map_div]
  rfl

/-- **Hermite–Biehler sums of index `κ`.** Let `E`, `E'` be holomorphic on the half-plane with
`E ≠ 0` and `‖E'‖ ≤ ‖E‖` there, `W` a divisor of `κ` points right of the line and `‖c‖ = 1`. If
`F = P_W E − c P_{W♯} E'` does not vanish identically on the half-plane, it has at most `κ` zeros
there. -/
theorem hermiteBiehler_index {E E' : ℂ → ℂ} {c : ℂ} (hE : DifferentiableOn ℂ E rightHalf)
    (hE' : DifferentiableOn ℂ E' rightHalf) (hne : ∀ s ∈ rightHalf, E s ≠ 0)
    (hle : ∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) (hc : ‖c‖ = 1) (W : Multiset ℂ)
    (hW : ∀ w ∈ W, w ∈ rightHalf)
    (hdiff : ∃ z ∈ rightHalf,
      divisorPoly W z * E z - c * divisorPoly (reflectDivisor W) z * E' z ≠ 0) :
    {s | s ∈ rightHalf ∧
      divisorPoly W s * E s - c * divisorPoly (reflectDivisor W) s * E' s = 0}.encard ≤
        Multiset.card W := by
  have hc0 := ne_zero_of_norm_eq_one hc
  have hθ : DifferentiableOn ℂ (fun s => E' s / E s) rightHalf := hE'.div hE hne
  have hθb : ∀ s ∈ rightHalf, ‖E' s / E s‖ ≤ 1 := fun s hs => by
    rw [norm_div]
    exact div_le_one_of_le₀ (hle s hs) (norm_nonneg _)
  have hB := isBlaschke_prod (c := c⁻¹) (by rw [norm_inv, hc, inv_one]) W hW
  -- zeros of `F` are agreements of `E'/E` with `c⁻¹ Π b_w`
  have key : ∀ s ∈ rightHalf,
      (divisorPoly W s * E s - c * divisorPoly (reflectDivisor W) s * E' s = 0 ↔
        E' s / E s = c⁻¹ * (W.map fun w => defectFactor w s).prod) := by
    intro s hs
    have hQ := divisorPoly_reflect_ne_zero hW hs
    have hEs := hne s hs
    rw [prod_defectFactor]
    constructor
    · intro h
      have h1 : c * divisorPoly (reflectDivisor W) s * E' s = divisorPoly W s * E s := by
        linear_combination -h
      field_simp
      linear_combination h1
    · intro h
      field_simp at h
      linear_combination -h
  have hset : {s | s ∈ rightHalf ∧
      divisorPoly W s * E s - c * divisorPoly (reflectDivisor W) s * E' s = 0} =
      {s | s ∈ rightHalf ∧ E' s / E s = c⁻¹ * (W.map fun w => defectFactor w s).prod} := by
    ext s
    exact ⟨fun h => ⟨h.1, (key s h.1).mp h.2⟩, fun h => ⟨h.1, (key s h.1).mpr h.2⟩⟩
  rw [hset]
  refine encard_agreements_le hθ hθb hB ?_
  obtain ⟨z, hz, hzne⟩ := hdiff
  exact ⟨z, hz, fun h => hzne ((key z hz).mpr h)⟩

theorem reflectDivisor_reflectDivisor (W : Multiset ℂ) :
    reflectDivisor (reflectDivisor W) = W := by
  rw [reflectDivisor, reflectDivisor, Multiset.map_map]
  exact (Multiset.map_congr rfl fun w _ => by simp).trans (Multiset.map_id' W)

/-- **The index is the number of zeros of the defect right of the line.** Let the defect
`P_{W₊} P_{W₋}` have the zeros `W₊` right of the line and `W₋` left of it. Then
`F = P_{W₊} P_{W₋} E − c P_{W₊♯} P_{W₋♯} E'` has at most `card W₊` zeros right of the line: the
zeros left of the line turn into Blaschke factors of the Schur function,
`(E'/E) · Π_{w ∈ W₋} b_{1 − w̄} = c⁻¹ Π_{w ∈ W₊} b_w`. -/
theorem hermiteBiehler_index_general {E E' : ℂ → ℂ} {c : ℂ}
    (hE : DifferentiableOn ℂ E rightHalf) (hE' : DifferentiableOn ℂ E' rightHalf)
    (hne : ∀ s ∈ rightHalf, E s ≠ 0) (hle : ∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) (hc : ‖c‖ = 1)
    (Wp Wm : Multiset ℂ) (hWp : ∀ w ∈ Wp, w ∈ rightHalf) (hWm : ∀ w ∈ Wm, w.re < 1 / 2)
    (hdiff : ∃ z ∈ rightHalf, divisorPoly Wp z * divisorPoly Wm z * E z -
      c * divisorPoly (reflectDivisor Wp) z * divisorPoly (reflectDivisor Wm) z * E' z ≠ 0) :
    {s | s ∈ rightHalf ∧ divisorPoly Wp s * divisorPoly Wm s * E s -
      c * divisorPoly (reflectDivisor Wp) s * divisorPoly (reflectDivisor Wm) s * E' s = 0}.encard ≤
        Multiset.card Wp := by
  have hc0 := ne_zero_of_norm_eq_one hc
  -- the reflected left zeros lie right of the line
  have hV : ∀ w ∈ reflectDivisor Wm, w ∈ rightHalf := by
    intro w hw
    rw [reflectDivisor, Multiset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    show (1 : ℝ) / 2 < (1 - (starRingEnd ℂ) u).re
    simp only [sub_re, one_re, conj_re]
    linarith [hWm u hu]
  have hBV := isBlaschke_prod (c := 1) norm_one (reflectDivisor Wm) hV
  have hβ : ∀ s, (1 : ℂ) * ((reflectDivisor Wm).map fun w => defectFactor w s).prod =
      divisorPoly (reflectDivisor Wm) s / divisorPoly Wm s := by
    intro s
    rw [one_mul, prod_defectFactor, reflectDivisor_reflectDivisor]
  -- the Schur function `(E'/E) · Π b_{1 − w̄}`
  have hθ : DifferentiableOn ℂ (fun s => E' s / E s *
      ((1 : ℂ) * ((reflectDivisor Wm).map fun w => defectFactor w s).prod)) rightHalf :=
    (hE'.div hE hne).mul hBV.differentiableOn
  have hθb : ∀ s ∈ rightHalf, ‖E' s / E s *
      ((1 : ℂ) * ((reflectDivisor Wm).map fun w => defectFactor w s).prod)‖ ≤ 1 := by
    intro s hs
    rw [norm_mul, norm_div]
    exact mul_le_one₀ (div_le_one_of_le₀ (hle s hs) (norm_nonneg _)) (norm_nonneg _)
      (hBV.norm_le_one hs)
  have hB := isBlaschke_prod (c := c⁻¹) (by rw [norm_inv, hc, inv_one]) Wp hWp
  have key : ∀ s ∈ rightHalf, (divisorPoly Wp s * divisorPoly Wm s * E s -
      c * divisorPoly (reflectDivisor Wp) s * divisorPoly (reflectDivisor Wm) s * E' s = 0 ↔
      E' s / E s * ((1 : ℂ) * ((reflectDivisor Wm).map fun w => defectFactor w s).prod) =
        c⁻¹ * (Wp.map fun w => defectFactor w s).prod) := by
    intro s hs
    have hQ := divisorPoly_reflect_ne_zero hWp hs
    have hEs := hne s hs
    have hPm : divisorPoly Wm s ≠ 0 := by
      rw [Ne, divisorPoly_eq_zero_iff]
      intro hmem
      have h1 : (1 : ℝ) / 2 < s.re := hs
      linarith [hWm s hmem]
    rw [hβ, prod_defectFactor]
    constructor
    · intro h
      have h1 : c * divisorPoly (reflectDivisor Wp) s * divisorPoly (reflectDivisor Wm) s * E' s =
          divisorPoly Wp s * divisorPoly Wm s * E s := by linear_combination -h
      field_simp
      linear_combination h1
    · intro h
      field_simp at h
      linear_combination -h
  have hset : {s | s ∈ rightHalf ∧ divisorPoly Wp s * divisorPoly Wm s * E s -
      c * divisorPoly (reflectDivisor Wp) s * divisorPoly (reflectDivisor Wm) s * E' s = 0} =
      {s | s ∈ rightHalf ∧ E' s / E s *
        ((1 : ℂ) * ((reflectDivisor Wm).map fun w => defectFactor w s).prod) =
          c⁻¹ * (Wp.map fun w => defectFactor w s).prod} := by
    ext s
    exact ⟨fun h => ⟨h.1, (key s h.1).mp h.2⟩, fun h => ⟨h.1, (key s h.1).mpr h.2⟩⟩
  rw [hset]
  refine encard_agreements_le hθ hθb hB ?_
  obtain ⟨z, hz, hzne⟩ := hdiff
  exact ⟨z, hz, fun h => hzne ((key z hz).mpr h)⟩

/-- **A family over a fixed part, with any polynomial defect.** Let `G` be entire without zero in
`Re w > 1` and with `‖G(w − 1)‖ ≤ ‖G(w)‖` there. For `Y ≥ 1` and a defect with the zeros `W₊` right
of the line and `W₋` left of it, the member
`P_{W₊} P_{W₋} G(2s) Y^s − c P_{W₊♯} P_{W₋♯} G(2s − 1) Y^{1−s}` has at most `card W₊` zeros right of
the line. The zeros of `G` inside the strip do not enter; the defect `(s − 1) Π_{j<m} (s + j)` has
index one for every `m`. -/
theorem pencil_index_general {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hne : ∀ w : ℂ, 1 < w.re → G w ≠ 0) (hle : ∀ w : ℂ, 1 < w.re → ‖G (w - 1)‖ ≤ ‖G w‖)
    {Y : ℝ} (hY : 1 ≤ Y) {c : ℂ} (hc : ‖c‖ = 1) (Wp Wm : Multiset ℂ)
    (hWp : ∀ w ∈ Wp, w ∈ rightHalf) (hWm : ∀ w ∈ Wm, w.re < 1 / 2)
    (hdiff : ∃ z ∈ rightHalf, divisorPoly Wp z * divisorPoly Wm z * pencilHalf G Y z -
      c * divisorPoly (reflectDivisor Wp) z * divisorPoly (reflectDivisor Wm) z *
        pencilDual G Y z ≠ 0) :
    {s | s ∈ rightHalf ∧ divisorPoly Wp s * divisorPoly Wm s * pencilHalf G Y s -
      c * divisorPoly (reflectDivisor Wp) s * divisorPoly (reflectDivisor Wm) s *
        pencilDual G Y s = 0}.encard ≤ Multiset.card Wp := by
  have hY0 : 0 < Y := by linarith
  exact hermiteBiehler_index_general (differentiable_pencilHalf hG hY0).differentiableOn
    (differentiable_pencilDual hG hY0).differentiableOn
    (fun s hs => pencilHalf_ne_zero hne hY0 hs) (fun s hs => norm_pencilDual_le hle hY hs) hc
    Wp Wm hWp hWm hdiff

/-! ### Index zero -/

/-- **Index zero.** A Hermite–Biehler sum without defect that is not identically zero right of the
line has no zero there. -/
theorem hermiteBiehler_indexZero {E E' : ℂ → ℂ} {c : ℂ} (hE : DifferentiableOn ℂ E rightHalf)
    (hE' : DifferentiableOn ℂ E' rightHalf) (hne : ∀ s ∈ rightHalf, E s ≠ 0)
    (hle : ∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) (hc : ‖c‖ = 1)
    (hdiff : ∃ z ∈ rightHalf, E z - c * E' z ≠ 0) {s : ℂ} (hs : s ∈ rightHalf) :
    E s - c * E' s ≠ 0 := by
  have hform : ∀ z : ℂ, divisorPoly 0 z * E z -
      c * divisorPoly (reflectDivisor 0) z * E' z = E z - c * E' z := by
    intro z
    rw [reflectDivisor, Multiset.map_zero, divisorPoly_zero]
    ring
  have h := hermiteBiehler_index hE hE' hne hle hc 0 (fun w hw => absurd hw (Multiset.notMem_zero w))
    (by simpa only [hform] using hdiff)
  simp only [hform, Multiset.card_zero, Nat.cast_zero, nonpos_iff_eq_zero,
    Set.encard_eq_zero] at h
  intro h0
  have hmem : s ∈ {s | s ∈ rightHalf ∧ E s - c * E' s = 0} := ⟨hs, h0⟩
  rw [h] at hmem
  exact hmem

/-- **The half-shift family over a fixed part is pure.** Let `G` be entire without zero in
`Re w > 1` and with `‖G(w − 1)‖ ≤ ‖G(w)‖` there. If `G(s + ½) − c G(s − ½)`, `‖c‖ = 1`, is not
identically zero right of the line, it has no zero there. -/
theorem halfShift_ne_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hne : ∀ w : ℂ, 1 < w.re → G w ≠ 0) (hle : ∀ w : ℂ, 1 < w.re → ‖G (w - 1)‖ ≤ ‖G w‖)
    {c : ℂ} (hc : ‖c‖ = 1)
    (hdiff : ∃ z ∈ rightHalf, G (z + 1 / 2) - c * G (z - 1 / 2) ≠ 0) {s : ℂ}
    (hs : s ∈ rightHalf) : G (s + 1 / 2) - c * G (s - 1 / 2) ≠ 0 := by
  have hre : ∀ z ∈ rightHalf, 1 < (z + 1 / 2).re := by
    intro z hz
    have h1 : (1 : ℝ) / 2 < z.re := hz
    simp only [add_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
    linarith
  have hE : Differentiable ℂ fun z : ℂ => G (z + 1 / 2) := fun z =>
    (hG (z + 1 / 2)).comp z (by fun_prop)
  have hE' : Differentiable ℂ fun z : ℂ => G (z - 1 / 2) := fun z =>
    (hG (z - 1 / 2)).comp z (by fun_prop)
  refine hermiteBiehler_indexZero (E := fun z => G (z + 1 / 2)) (E' := fun z => G (z - 1 / 2))
    hE.differentiableOn hE'.differentiableOn (fun z hz => hne _ (hre z hz)) (fun z hz => ?_) hc
    hdiff hs
  have h := hle _ (hre z hz)
  rwa [show z + 1 / 2 - 1 = z - 1 / 2 by ring] at h

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown in
/-- **Taylor's theorem as index zero.** All zeros of `ξ(s + ½) + ξ(s − ½)` and of
`ξ(s + ½) − ξ(s − ½)` lie on the line `Re s = ½`. -/
theorem re_eq_half_of_xi_halfShift_eq_zero {c : ℂ} (hc : c = 1 ∨ c = -1) {s : ℂ}
    (h : xi (s + 1 / 2) - c * xi (s - 1 / 2) = 0) : s.re = 1 / 2 := by
  have hcn : ‖c‖ = 1 := by
    rcases hc with rfl | rfl <;> simp
  have hcc : c * c = 1 := by
    rcases hc with rfl | rfl <;> norm_num
  obtain ⟨hne, hle, -⟩ := xi_mem_pencil_class
  -- the sum is not identically zero right of the line: a zero of `ξ` would repeat at `ρ + 1`
  have hdiff : ∃ z ∈ rightHalf, xi (z + 1 / 2) - c * xi (z - 1 / 2) ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    obtain ⟨ρ, hρ⟩ := xiZeros_infinite.nonempty
    have hρ0 : xi ρ = 0 := hρ
    have hρre : 0 < ρ.re := re_pos_of_xi_eq_zero hρ0
    have hmem : ρ + 1 / 2 ∈ rightHalf := by
      show (1 : ℝ) / 2 < (ρ + 1 / 2).re
      simp only [add_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
      linarith
    have h0 : xi (ρ + 1 / 2 + 1 / 2) - c * xi (ρ + 1 / 2 - 1 / 2) = 0 := by
      by_contra hne'
      exact hcon (ρ + 1 / 2) ⟨hmem, hne'⟩
    rw [show ρ + 1 / 2 - 1 / 2 = ρ by ring, hρ0, mul_zero, sub_zero,
      show ρ + 1 / 2 + 1 / 2 = ρ + 1 by ring] at h0
    refine hne (ρ + 1) ?_ h0
    simp only [add_re, one_re]
    linarith
  have key : ∀ z ∈ rightHalf, xi (z + 1 / 2) - c * xi (z - 1 / 2) ≠ 0 := fun z hz =>
    halfShift_ne_zero xi_differentiable hne hle hcn hdiff hz
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · -- reflect: `F(1 − s) = −c F(s)`
    have hmem : 1 - s ∈ rightHalf := by
      show (1 : ℝ) / 2 < (1 - s).re
      simp only [sub_re, one_re]
      linarith
    have e1 : xi (1 - s + 1 / 2) = xi (s - 1 / 2) := by
      rw [show 1 - s + 1 / 2 = 1 - (s - 1 / 2) by ring, xi_one_sub]
    have e2 : xi (1 - s - 1 / 2) = xi (s + 1 / 2) := by
      rw [show 1 - s - 1 / 2 = 1 - (s + 1 / 2) by ring, xi_one_sub]
    refine key (1 - s) hmem ?_
    rw [e1, e2]
    linear_combination (-c) * h - xi (s - 1 / 2) * hcc
  · exact key s hgt h

/-! ### The parity law at index `κ` -/

/-- A set stable under complex conjugation has at most half of its points above the real axis. -/
theorem two_mul_encard_upper_le_encard {Z : Set ℂ} (hZ : ∀ s ∈ Z, (starRingEnd ℂ) s ∈ Z) :
    2 * {s | s ∈ Z ∧ 0 < s.im}.encard ≤ Z.encard := by
  have hdisj : Disjoint {s | s ∈ Z ∧ 0 < s.im} ((starRingEnd ℂ) '' {s | s ∈ Z ∧ 0 < s.im}) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, hs⟩ ⟨t, ⟨-, ht⟩, rfl⟩
    rw [conj_im] at hs
    linarith
  have hsub : {s | s ∈ Z ∧ 0 < s.im} ∪ (starRingEnd ℂ) '' {s | s ∈ Z ∧ 0 < s.im} ⊆ Z := by
    rintro s (⟨hs, -⟩ | ⟨t, ⟨ht, -⟩, rfl⟩)
    · exact hs
    · exact hZ t ht
  have hinj : Function.Injective (starRingEnd ℂ : ℂ → ℂ) := (starRingEnd ℂ).injective
  calc 2 * {s | s ∈ Z ∧ 0 < s.im}.encard
      = {s | s ∈ Z ∧ 0 < s.im}.encard + ((starRingEnd ℂ) '' {s | s ∈ Z ∧ 0 < s.im}).encard := by
        rw [hinj.encard_image, two_mul]
    _ = ({s | s ∈ Z ∧ 0 < s.im} ∪ (starRingEnd ℂ) '' {s | s ∈ Z ∧ 0 < s.im}).encard :=
        (Set.encard_union_eq hdisj).symm
    _ ≤ Z.encard := Set.encard_le_encard hsub

/-- **The parity law at index `κ`.** A real function with at most `κ` zeros right of the line has
at most `κ/2` of them above the real axis. -/
theorem two_mul_encard_upper_zeros_le {F : ℂ → ℂ} {κ : ℕ}
    (hreal : ∀ s ∈ rightHalf, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s))
    (hcount : {s | s ∈ rightHalf ∧ F s = 0}.encard ≤ κ) :
    2 * {s | s ∈ rightHalf ∧ 0 < s.im ∧ F s = 0}.encard ≤ κ := by
  have hZ : ∀ s ∈ {s | s ∈ rightHalf ∧ F s = 0},
      (starRingEnd ℂ) s ∈ {s | s ∈ rightHalf ∧ F s = 0} := by
    rintro s ⟨hs, h0⟩
    exact ⟨conj_mem_rightHalf hs, by rw [hreal s hs, h0, map_zero]⟩
  have hset : {s | s ∈ rightHalf ∧ 0 < s.im ∧ F s = 0} =
      {s | s ∈ {s | s ∈ rightHalf ∧ F s = 0} ∧ 0 < s.im} := by
    ext s
    simp only [Set.mem_setOf_eq]
    tauto
  rw [hset]
  exact (two_mul_encard_upper_le_encard hZ).trans hcount

/-! ### The bound is attained at every index -/

/-- `e^{s−½} + e^{½−s}` has no zero right of the line. -/
theorem exp_add_exp_ne_zero {s : ℂ} (hs : s ∈ rightHalf) :
    Complex.exp (s - 1 / 2) + Complex.exp (1 / 2 - s) ≠ 0 := by
  intro h
  have h1 : Complex.exp (s - 1 / 2) = -Complex.exp (1 / 2 - s) := by linear_combination h
  have h2 := congrArg norm h1
  rw [norm_neg, Complex.norm_exp, Complex.norm_exp, Real.exp_eq_exp] at h2
  have hs' : (1 : ℝ) / 2 < s.re := hs
  simp only [sub_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self'] at h2
  linarith

/-- **The index bound is attained by every configuration.** For every divisor `W` right of the
line the `cosh` model `P_W P_{W♯} (e^{s−½} + e^{½−s})` is a Hermite–Biehler sum
`P_W E + P_{W♯} E'` with `E ≠ 0`, `‖E'‖ ≤ ‖E‖` right of the line, and right of the line it vanishes
exactly on `W`. -/
theorem index_attained (W : Multiset ℂ) (hW : ∀ w ∈ W, w ∈ rightHalf) :
    ∃ E E' : ℂ → ℂ, Differentiable ℂ E ∧ Differentiable ℂ E' ∧ (∀ s ∈ rightHalf, E s ≠ 0) ∧
      (∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) ∧
      ∀ s ∈ rightHalf, (divisorPoly W s * E s -
        (-1 : ℂ) * divisorPoly (reflectDivisor W) s * E' s = 0 ↔ s ∈ W) := by
  refine ⟨fun s => Complex.exp (s - 1 / 2) * divisorPoly (reflectDivisor W) s,
    fun s => Complex.exp (1 / 2 - s) * divisorPoly W s, ?_, ?_, fun s hs => ?_, fun s hs => ?_,
    fun s hs => ?_⟩
  · exact (Complex.differentiable_exp.comp (differentiable_id.sub (differentiable_const _))).mul
      (differentiable_divisorPoly _)
  · exact (Complex.differentiable_exp.comp ((differentiable_const _).sub differentiable_id)).mul
      (differentiable_divisorPoly _)
  · exact mul_ne_zero (Complex.exp_ne_zero _) (divisorPoly_reflect_ne_zero hW hs)
  · have hs' : (1 : ℝ) / 2 < s.re := hs
    have hexp : ‖Complex.exp (1 / 2 - s)‖ ≤ ‖Complex.exp (s - 1 / 2)‖ := by
      rw [Complex.norm_exp, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [sub_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
      linarith
    have hpoly : ‖divisorPoly W s‖ ≤ ‖divisorPoly (reflectDivisor W) s‖ := by
      have hr : ‖divisorPoly (reflectDivisor W) s‖ =
          (W.map fun w => ‖s - (1 - (starRingEnd ℂ) w)‖).prod := by
        rw [norm_divisorPoly, reflectDivisor, Multiset.map_map]
        rfl
      rw [norm_divisorPoly, hr]
      exact Multiset.prod_map_le_prod_map₀ _ _ (fun w _ => norm_nonneg _)
        fun w hw => norm_sub_le_norm_sub_reflect (hW w hw) hs
    simp only [norm_mul]
    exact mul_le_mul hexp hpoly (norm_nonneg _) (norm_nonneg _)
  · have hQ := divisorPoly_reflect_ne_zero hW hs
    have hexp := exp_add_exp_ne_zero hs
    have hform : divisorPoly W s * (Complex.exp (s - 1 / 2) * divisorPoly (reflectDivisor W) s) -
        (-1 : ℂ) * divisorPoly (reflectDivisor W) s * (Complex.exp (1 / 2 - s) * divisorPoly W s) =
        divisorPoly W s * (divisorPoly (reflectDivisor W) s *
          (Complex.exp (s - 1 / 2) + Complex.exp (1 / 2 - s))) := by
      ring
    rw [hform, mul_eq_zero, divisorPoly_eq_zero_iff]
    exact ⟨fun h => h.resolve_right (mul_ne_zero hQ hexp), Or.inl⟩

end

end GaloisForLFunctions.InfiniteRankPurityTheory
