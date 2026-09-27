import GaloisForLFunctions.RHTower.HodgeOffLineFlatnessLaw

/-!
# Division by a finite divisor and exponential-polynomial shift operators

For a list `L` of distinct points `γ` in the strip `|Im γ| ≤ 1/2`, with orders `m`, at each of
which `ĝ` has a local factor `(z - γ)^m u(z)`, the composite resolvent division
`D_L g = D_{γ₁}^{m₁} ⋯ D_{γ_k}^{m_k} g` satisfies (`multiResolvent_spec`, `multiResolvent_tail`)

* `Π (z - γ)^m · (D_L g)^ = ĝ`, and `(D_L g)^` does not vanish at the points of `L`;
* `∫_{|x|≥X} ‖D_L g‖ e^{c|x|} ≤ 2^{Σm} ∫_{|u|≥X} ‖g‖ e^{(c + 3Σm/2)|u|}`.

The tail bound does not depend on the positions of the points: tight clusters cost nothing.
When `Σm ≥ 2`, the division is `D_a D_b g₂` (`multiResolvent_two_step`), which gives two
continuous integrable derivatives (`resolvent_pair_calculus`).

The shift operator `g ↦ Σ c_k g(· - kκ)` has symbol `Q(e^{iκz})`, where `Q = Σ c_k X^k`
(`paperFT_polyShiftOp`).
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Division by a finite divisor -/

/-- Composite resolvent division along a list of points with orders. -/
def multiResolvent (L : List (ℂ × ℕ)) (g : ℝ → ℂ) : ℝ → ℂ :=
  L.foldr (fun p acc => iterResolvent p.1 p.2 acc) g

theorem multiResolvent_nil (g : ℝ → ℂ) : multiResolvent [] g = g := rfl

theorem multiResolvent_cons (p : ℂ × ℕ) (L : List (ℂ × ℕ)) (g : ℝ → ℂ) :
    multiResolvent (p :: L) g = iterResolvent p.1 p.2 (multiResolvent L g) := rfl

/-- The divisor polynomial `Π (z - γ)^m` of a list, evaluated. -/
def divisorEval (L : List (ℂ × ℕ)) (z : ℂ) : ℂ := (L.map fun p => (z - p.1) ^ p.2).prod

theorem divisorEval_cons (p : ℂ × ℕ) (L : List (ℂ × ℕ)) (z : ℂ) :
    divisorEval (p :: L) z = (z - p.1) ^ p.2 * divisorEval L z := by
  simp [divisorEval]

theorem divisorEval_ne_zero {L : List (ℂ × ℕ)} {z : ℂ} (h : ∀ p ∈ L, z ≠ p.1) :
    divisorEval L z ≠ 0 := by
  induction L with
  | nil => simp [divisorEval]
  | cons p L ih =>
    rw [divisorEval_cons]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (h p (by simp))))
      (ih fun q hq => h q (by simp [hq]))

/-- The total order `Σ m` of a list. -/
def orderSum (L : List (ℂ × ℕ)) : ℕ := (L.map Prod.snd).sum

theorem orderSum_cons (p : ℂ × ℕ) (L : List (ℂ × ℕ)) :
    orderSum (p :: L) = p.2 + orderSum L := by simp [orderSum]

/-- Hypotheses under which the composite division is legitimate: distinct points in the strip,
at each of which `ĝ` has a local factor of the listed order. -/
def DivisorData (L : List (ℂ × ℕ)) (g : ℝ → ℂ) : Prop :=
  L.Pairwise (fun p q => p.1 ≠ q.1) ∧ (∀ p ∈ L, |p.1.im| ≤ 1 / 2) ∧
    ∀ p ∈ L, ∃ u : ℂ → ℂ, ContinuousAt u p.1 ∧ u p.1 ≠ 0 ∧
      paperFT g =ᶠ[𝓝 p.1] fun z => (z - p.1) ^ p.2 * u z

theorem DivisorData.tail {p : ℂ × ℕ} {L : List (ℂ × ℕ)} {g : ℝ → ℂ}
    (h : DivisorData (p :: L) g) : DivisorData L g :=
  ⟨(List.pairwise_cons.mp h.1).2, fun q hq => h.2.1 q (by simp [hq]),
    fun q hq => h.2.2 q (by simp [hq])⟩

/-- **Division by a finite divisor.** Under `DivisorData`, the composite resolvent decays
super-exponentially, `Π(z-γ)^m · (D_L g)^ = ĝ`, `(D_L g)^` does not vanish at the points of `L`,
and at any other point where `ĝ` has a local factorisation, `(D_L g)^` has one of the same
order. -/
theorem multiResolvent_spec (L : List (ℂ × ℕ)) :
    ∀ {g : ℝ → ℂ}, SuperExpDecay g → DivisorData L g →
      SuperExpDecay (multiResolvent L g) ∧
      (∀ z, divisorEval L z * paperFT (multiResolvent L g) z = paperFT g z) ∧
      (∀ p ∈ L, paperFT (multiResolvent L g) p.1 ≠ 0) ∧
      (∀ (q : ℂ) (k : ℕ) (u : ℂ → ℂ), (∀ p ∈ L, q ≠ p.1) → ContinuousAt u q → u q ≠ 0 →
        paperFT g =ᶠ[𝓝 q] (fun z => (z - q) ^ k * u z) →
        ∃ u' : ℂ → ℂ, ContinuousAt u' q ∧ u' q ≠ 0 ∧
          paperFT (multiResolvent L g) =ᶠ[𝓝 q] fun z => (z - q) ^ k * u' z) := by
  induction L with
  | nil =>
    intro g hg _
    refine ⟨hg, fun z => by simp [multiResolvent_nil, divisorEval], fun p hp => by simp at hp,
      fun q k u _ hu hu0 hloc => ⟨u, hu, hu0, by simpa [multiResolvent_nil] using hloc⟩⟩
  | cons p L ih =>
    intro g hg hD
    obtain ⟨hpw, him, hloc⟩ := hD
    have hpw' := List.pairwise_cons.mp hpw
    have hdist : ∀ q ∈ L, p.1 ≠ q.1 := hpw'.1
    obtain ⟨hG, hprod, hnode, htrack⟩ := ih hg (DivisorData.tail ⟨hpw, him, hloc⟩)
    set G := multiResolvent L g
    obtain ⟨up, hup, hup0, hlocp⟩ := hloc p (by simp)
    obtain ⟨u', hu', hu'0, hloc'⟩ := htrack p.1 p.2 up (fun q hq => hdist q hq) hup hup0 hlocp
    have hspec := iterResolvent_spec hG (him p (by simp)) hu' hloc' p.2 le_rfl
    obtain ⟨hD, hlocD, hprodD⟩ := hspec
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [multiResolvent_cons]; exact hD
    · intro z
      rw [multiResolvent_cons, divisorEval_cons, mul_comm ((z - p.1) ^ p.2), mul_assoc, hprodD z,
        hprod z]
    · intro q hq
      rw [multiResolvent_cons]
      rcases List.mem_cons.mp hq with rfl | hqL
      · have h := hlocD.eq_of_nhds
        rw [Nat.sub_self, pow_zero, one_mul] at h
        rw [h]; exact hu'0
      · have hne : q.1 ≠ p.1 := fun h => hdist q hqL h.symm
        have hGq : paperFT G =ᶠ[𝓝 q.1] fun z => (z - q.1) ^ 0 * paperFT G z := by
          exact Eventually.of_forall fun z => by simp
        have htr := iterResolvent_eventually_ne hG (him p (by simp)) hu' hloc' hne hGq p.2 le_rfl
        have h := htr.eq_of_nhds
        rw [pow_zero, one_mul] at h
        rw [h]
        exact div_ne_zero (hnode q hqL) (pow_ne_zero _ (sub_ne_zero.mpr hne))
    · intro q k u hq hu hu0 hlocq
      obtain ⟨v, hv, hv0, hlocv⟩ := htrack q k u (fun r hr => hq r (by simp [hr])) hu hu0 hlocq
      have hne : q ≠ p.1 := hq p (by simp)
      have htr := iterResolvent_eventually_ne hG (him p (by simp)) hu' hloc' hne hlocv p.2 le_rfl
      refine ⟨fun z => v z / (z - p.1) ^ p.2, hv.div ((continuousAt_id.sub continuousAt_const).pow _)
        (pow_ne_zero _ (sub_ne_zero.mpr hne)), div_ne_zero hv0 (pow_ne_zero _ (sub_ne_zero.mpr hne)),
        ?_⟩
      rw [multiResolvent_cons]; exact htr

/-- The local factor of the partial division at the head point. -/
theorem DivisorData.head_local {p : ℂ × ℕ} {L : List (ℂ × ℕ)} {g : ℝ → ℂ} (hg : SuperExpDecay g)
    (hD : DivisorData (p :: L) g) : ∃ u' : ℂ → ℂ, ContinuousAt u' p.1 ∧ u' p.1 ≠ 0 ∧
      paperFT (multiResolvent L g) =ᶠ[𝓝 p.1] fun z => (z - p.1) ^ p.2 * u' z := by
  obtain ⟨-, -, -, htrack⟩ := multiResolvent_spec L hg hD.tail
  obtain ⟨up, hup, hup0, hlocp⟩ := hD.2.2 p (by simp)
  exact htrack p.1 p.2 up (fun q hq => (List.pairwise_cons.mp hD.1).1 q hq) hup hup0 hlocp

/-- **Tail of the composite division.**
`∫_{|x|≥X} ‖D_L g‖ e^{c|x|} ≤ 2^{Σm} ∫_{|u|≥X} ‖g‖ e^{(c + 3Σm/2)|u|}`. -/
theorem multiResolvent_tail (L : List (ℂ × ℕ)) :
    ∀ {g : ℝ → ℂ}, SuperExpDecay g → DivisorData L g → ∀ c X : ℝ, 0 ≤ c →
      expTail (multiResolvent L g) c X ≤
        2 ^ orderSum L * expTail g (c + 3 / 2 * orderSum L) X := by
  induction L with
  | nil => intro g _ _ c X _; simp [multiResolvent_nil, orderSum]
  | cons p L ih =>
    intro g hg hD c X hc
    have hG := (multiResolvent_spec L hg hD.tail).1
    obtain ⟨u', hu', -, hloc'⟩ := hD.head_local hg
    have h1 := expTail_iterResolvent_le hG (hD.2.1 p (by simp)) hu' hloc' p.2 le_rfl c X hc
    have h2 := ih hg hD.tail (c + 3 / 2 * p.2) X (by positivity)
    rw [multiResolvent_cons, orderSum_cons]
    calc expTail (iterResolvent p.1 p.2 (multiResolvent L g)) c X
        ≤ 2 ^ p.2 * (2 ^ orderSum L * expTail g (c + 3 / 2 * p.2 + 3 / 2 * orderSum L) X) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = 2 ^ (p.2 + orderSum L) * expTail g (c + 3 / 2 * ((p.2 + orderSum L : ℕ) : ℝ)) X := by
          rw [pow_add]; push_cast; ring_nf

theorem pow_mul_expTail_le {g : ℝ → ℂ} (hg : SuperExpDecay g) {j N : ℕ} (hjN : j ≤ N) (c X : ℝ) :
    2 ^ j * expTail g (c + 3 / 2 * j) X ≤ 2 ^ N * expTail g (c + 3 / 2 * N) X := by
  refine mul_le_mul (pow_le_pow_right₀ (by norm_num) hjN) ?_ (expTail_nonneg _ _ _) (by positivity)
  apply expTail_mono_weight hg
  have : (j : ℝ) ≤ N := by exact_mod_cast hjN
  linarith

/-- **Two outermost divisions.** If every order is positive and `Σm ≥ 2`, the composite division
is `D_a D_b g₂` for points `a, b` of the list and a super-exponentially decaying `g₂`, with the
tails of `g₂` and `D_b g₂` controlled like that of `D_L g`. -/
theorem multiResolvent_two_step {L : List (ℂ × ℕ)} {g : ℝ → ℂ} (hg : SuperExpDecay g)
    (hD : DivisorData L g) (hpos : ∀ p ∈ L, 1 ≤ p.2) (h2 : 2 ≤ orderSum L) :
    ∃ a b : ℂ, ∃ g₂ : ℝ → ℂ, (∃ p ∈ L, a = p.1) ∧ (∃ p ∈ L, b = p.1) ∧ SuperExpDecay g₂ ∧
      SuperExpDecay (resolventDiv b g₂) ∧
      multiResolvent L g = resolventDiv a (resolventDiv b g₂) ∧
      (∀ c X : ℝ, 0 ≤ c → expTail g₂ c X ≤
        2 ^ orderSum L * expTail g (c + 3 / 2 * orderSum L) X) ∧
      (∀ c X : ℝ, 0 ≤ c → expTail (resolventDiv b g₂) c X ≤
        2 ^ orderSum L * expTail g (c + 3 / 2 * orderSum L) X) := by
  rcases L with _ | ⟨p, L'⟩
  · simp [orderSum] at h2
  set G := multiResolvent L' g
  have hG := (multiResolvent_spec L' hg hD.tail).1
  have hGt := multiResolvent_tail L' hg hD.tail
  obtain ⟨u', hu', -, hloc'⟩ := hD.head_local hg
  have himp := hD.2.1 p (by simp)
  have hsum : orderSum (p :: L') = p.2 + orderSum L' := orderSum_cons p L'
  -- the tail of `D_p^k G`
  have hiter : ∀ k, k ≤ p.2 → ∀ c X : ℝ, 0 ≤ c → expTail (iterResolvent p.1 k G) c X ≤
      2 ^ orderSum (p :: L') * expTail g (c + 3 / 2 * orderSum (p :: L')) X := by
    intro k hk c X hc
    have h1 := expTail_iterResolvent_le hG himp hu' hloc' k hk c X hc
    have h2' := hGt (c + 3 / 2 * k) X (by positivity)
    calc expTail (iterResolvent p.1 k G) c X
        ≤ 2 ^ k * (2 ^ orderSum L' * expTail g (c + 3 / 2 * k + 3 / 2 * orderSum L') X) :=
          h1.trans (mul_le_mul_of_nonneg_left h2' (by positivity))
      _ = 2 ^ (k + orderSum L') * expTail g (c + 3 / 2 * ((k + orderSum L' : ℕ) : ℝ)) X := by
          rw [pow_add]; push_cast; ring_nf
      _ ≤ _ := pow_mul_expTail_le hg (by rw [hsum]; omega) c X
  rcases Nat.lt_or_ge p.2 2 with hlt | hge
  · -- `p.2 = 1`: the second division comes from the next point
    have hp1 : p.2 = 1 := by have := hpos p (by simp); omega
    rcases L' with _ | ⟨q, L''⟩
    · simp [orderSum, hp1] at h2
    have hDq : DivisorData (q :: L'') g := hD.tail
    set G'' := multiResolvent L'' g
    have hG'' := (multiResolvent_spec L'' hg hDq.tail).1
    have hG''t := multiResolvent_tail L'' hg hDq.tail
    obtain ⟨v', hv', -, hlocv⟩ := hDq.head_local hg
    have himq := hDq.2.1 q (by simp)
    have hq1 := hpos q (by simp)
    have hsum' : orderSum (p :: q :: L'') = p.2 + (q.2 + orderSum L'') := by
      rw [orderSum_cons, orderSum_cons]
    have hqiter : ∀ k, k ≤ q.2 → ∀ c X : ℝ, 0 ≤ c → expTail (iterResolvent q.1 k G'') c X ≤
        2 ^ orderSum (p :: q :: L'') * expTail g (c + 3 / 2 * orderSum (p :: q :: L'')) X := by
      intro k hk c X hc
      have h1 := expTail_iterResolvent_le hG'' himq hv' hlocv k hk c X hc
      have h2' := hG''t (c + 3 / 2 * k) X (by positivity)
      calc expTail (iterResolvent q.1 k G'') c X
          ≤ 2 ^ k * (2 ^ orderSum L'' * expTail g (c + 3 / 2 * k + 3 / 2 * orderSum L'') X) :=
            h1.trans (mul_le_mul_of_nonneg_left h2' (by positivity))
        _ = 2 ^ (k + orderSum L'') * expTail g (c + 3 / 2 * ((k + orderSum L'' : ℕ) : ℝ)) X := by
            rw [pow_add]; push_cast; ring_nf
        _ ≤ _ := pow_mul_expTail_le hg (by rw [hsum']; omega) c X
    have hspec := iterResolvent_spec hG'' himq hv' hlocv
    refine ⟨p.1, q.1, iterResolvent q.1 (q.2 - 1) G'', ⟨p, by simp, rfl⟩, ⟨q, by simp, rfl⟩,
      (hspec (q.2 - 1) (by omega)).1, ?_, ?_, fun c X hc => hqiter _ (by omega) c X hc, ?_⟩
    · rw [← iterResolvent_succ, show q.2 - 1 + 1 = q.2 by omega]
      exact (hspec q.2 le_rfl).1
    · rw [multiResolvent_cons, hp1, show (1 : ℕ) = 0 + 1 from rfl, iterResolvent_succ,
        iterResolvent_zero, ← iterResolvent_succ, show q.2 - 1 + 1 = q.2 by omega]
      rfl
    · intro c X hc
      rw [← iterResolvent_succ, show q.2 - 1 + 1 = q.2 by omega]
      exact hqiter _ le_rfl c X hc
  · -- `p.2 ≥ 2`: both divisions at `p`
    have hspec := iterResolvent_spec hG himp hu' hloc'
    refine ⟨p.1, p.1, iterResolvent p.1 (p.2 - 2) G, ⟨p, by simp, rfl⟩, ⟨p, by simp, rfl⟩,
      (hspec (p.2 - 2) (by omega)).1, ?_, ?_, fun c X hc => hiter _ (by omega) c X hc, ?_⟩
    · rw [← iterResolvent_succ, show p.2 - 2 + 1 = p.2 - 1 by omega]
      exact (hspec (p.2 - 1) (by omega)).1
    · rw [multiResolvent_cons, ← iterResolvent_succ, ← iterResolvent_succ,
        show p.2 - 2 + 1 + 1 = p.2 by omega]
    · intro c X hc
      rw [← iterResolvent_succ, show p.2 - 2 + 1 = p.2 - 1 by omega]
      exact hiter _ (by omega) c X hc

/-- **Calculus of a double resolvent division.** For `h = D_a D_b g₂` with all three stages
super-exponentially decaying, `h` is twice differentiable with explicit continuous integrable
derivatives, `‖h'‖₁ ≤ (1+Γ)B` and `‖h''‖₁ ≤ (1+Γ)²B`, where `|a|, |b| ≤ Γ` and `B` bounds the
`L¹` norms of the three stages. -/
theorem resolvent_pair_calculus {a b : ℂ} {g₂ : ℝ → ℂ} (hg₂ : SuperExpDecay g₂)
    (hgp : SuperExpDecay (resolventDiv b g₂))
    (hh : SuperExpDecay (resolventDiv a (resolventDiv b g₂))) {Γ B : ℝ} (ha : ‖a‖ ≤ Γ)
    (hb : ‖b‖ ≤ Γ) (hB1 : ∫ x, ‖resolventDiv a (resolventDiv b g₂) x‖ ≤ B)
    (hB2 : ∫ x, ‖resolventDiv b g₂ x‖ ≤ B) (hB3 : ∫ x, ‖g₂ x‖ ≤ B) :
    ∃ k₁ k₂ : ℝ → ℂ, (∀ x, HasDerivAt (resolventDiv a (resolventDiv b g₂)) (k₁ x) x) ∧
      (∀ x, HasDerivAt k₁ (k₂ x) x) ∧ Continuous k₁ ∧ Continuous k₂ ∧ Integrable k₁ ∧
      Integrable k₂ ∧ (∫ x, ‖k₁ x‖) ≤ (1 + Γ) * B ∧ (∫ x, ‖k₂ x‖) ≤ (1 + Γ) ^ 2 * B := by
  set gp := resolventDiv b g₂ with hgpdef
  set h := resolventDiv a gp with hhdef
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans ha
  have hB : 0 ≤ B := (integral_nonneg fun _ => norm_nonneg _).trans hB3
  set k₁ : ℝ → ℂ := fun x => -I * a * h x - I * gp x with hk₁
  set p₁ : ℝ → ℂ := fun x => -I * b * gp x - I * g₂ x with hp₁
  set k₂ : ℝ → ℂ := fun x => -I * a * k₁ x - I * p₁ x with hk₂
  have hdk : ∀ x, HasDerivAt h (k₁ x) x := fun x => hasDerivAt_resolventDiv hgp a x
  have hdp : ∀ x, HasDerivAt gp (p₁ x) x := fun x => hasDerivAt_resolventDiv hg₂ b x
  have hdk₁ : ∀ x, HasDerivAt k₁ (k₂ x) x := by
    intro x
    exact ((hdk x).const_mul (-I * a)).sub ((hdp x).const_mul I) |>.congr_deriv (by
      simp only [hk₂]; try ring)
  have ck : Continuous h := hh.1
  have cgp : Continuous gp := hgp.1
  have cg₂ : Continuous g₂ := hg₂.1
  have ck₁ : Continuous k₁ := by simp only [hk₁]; fun_prop
  have cp₁ : Continuous p₁ := by simp only [hp₁]; fun_prop
  have ck₂ : Continuous k₂ := by simp only [hk₂]; fun_prop
  have ik : Integrable h := hh.integrable
  have igp : Integrable gp := hgp.integrable
  have ig₂ : Integrable g₂ := hg₂.integrable
  have ik₁ : Integrable k₁ := (ik.const_mul _).sub (igp.const_mul _)
  have ip₁ : Integrable p₁ := (igp.const_mul _).sub (ig₂.const_mul _)
  have ik₂ : Integrable k₂ := (ik₁.const_mul _).sub (ip₁.const_mul _)
  have hnI : ‖I‖ = 1 := Complex.norm_I
  have nk₁ : ∫ x, ‖k₁ x‖ ≤ ‖a‖ * (∫ x, ‖h x‖) + ∫ x, ‖gp x‖ := by
    rw [← integral_const_mul, ← integral_add (ik.norm.const_mul _) igp.norm]
    refine integral_mono ik₁.norm ((ik.norm.const_mul _).add igp.norm) fun x => ?_
    simp only [hk₁]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, hnI]; simp
  have np₁ : ∫ x, ‖p₁ x‖ ≤ ‖b‖ * (∫ x, ‖gp x‖) + ∫ x, ‖g₂ x‖ := by
    rw [← integral_const_mul, ← integral_add (igp.norm.const_mul _) ig₂.norm]
    refine integral_mono ip₁.norm ((igp.norm.const_mul _).add ig₂.norm) fun x => ?_
    simp only [hp₁]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, hnI]; simp
  have nk₂ : ∫ x, ‖k₂ x‖ ≤ ‖a‖ * (∫ x, ‖k₁ x‖) + ∫ x, ‖p₁ x‖ := by
    rw [← integral_const_mul, ← integral_add (ik₁.norm.const_mul _) ip₁.norm]
    refine integral_mono ik₂.norm ((ik₁.norm.const_mul _).add ip₁.norm) fun x => ?_
    simp only [hk₂]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, hnI]; simp
  have hna := norm_nonneg a
  have hnb := norm_nonneg b
  have e1 : ‖a‖ * (∫ x, ‖h x‖) ≤ Γ * B := mul_le_mul ha hB1 (integral_nonneg fun _ => norm_nonneg _) hΓ
  have b₁ : ∫ x, ‖k₁ x‖ ≤ (1 + Γ) * B := by nlinarith
  have e2 : ‖a‖ * (∫ x, ‖k₁ x‖) ≤ Γ * ((1 + Γ) * B) :=
    mul_le_mul ha b₁ (integral_nonneg fun _ => norm_nonneg _) hΓ
  have e3 : ‖b‖ * (∫ x, ‖gp x‖) ≤ Γ * B := mul_le_mul hb hB2 (integral_nonneg fun _ => norm_nonneg _) hΓ
  refine ⟨k₁, k₂, hdk, hdk₁, ck₁, ck₂, ik₁, ik₂, b₁, ?_⟩
  nlinarith

/-! ## Shift operators with an exponential-polynomial symbol -/

/-- The shift operator `g ↦ Σ_k c_k g(· - kκ)` with symbol `Q(e^{iκz})`, `c_k` the coefficients
of `Q`. -/
def polyShiftOp (Q : ℂ[X]) (κ : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * g (x - k * κ)

/-- The coefficient mass `Σ_k ‖c_k‖`. -/
def coeffMass (Q : ℂ[X]) : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖

theorem coeffMass_nonneg (Q : ℂ[X]) : 0 ≤ coeffMass Q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem SuperExpDecay.finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ s, SuperExpDecay (g i)) : SuperExpDecay (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨continuous_const, fun c => ?_⟩
    simp
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have e : (fun x => ∑ i ∈ insert a s, g i x) = g a + fun x => ∑ i ∈ s, g i x :=
      funext fun x => by simp [Finset.sum_insert ha]
    rw [e]; exact h1.add h2

theorem SuperExpDecay.polyShiftOp {g : ℝ → ℂ} (hg : SuperExpDecay g) (Q : ℂ[X]) (κ : ℝ) :
    SuperExpDecay (polyShiftOp Q κ g) :=
  SuperExpDecay.finset_sum _ fun k _ => (hg.comp_sub (k * κ)).const_mul (Q.coeff k)

theorem paperFT_polyShiftOp {g : ℝ → ℂ} {z : ℂ}
    (hg : Integrable (fun u => g u * Complex.exp (I * z * u))) (Q : ℂ[X]) (κ : ℝ) :
    paperFT (polyShiftOp Q κ g) z = Q.eval (Complex.exp (I * z * κ)) * paperFT g z := by
  have hint : ∀ k ∈ Finset.range (Q.natDegree + 1), Integrable
      (fun u : ℝ => Q.coeff k * g (u - k * κ) * Complex.exp (I * z * u)) := by
    intro k _
    have := (integrable_comp_sub_mul_cexp hg (k * κ)).const_mul (Q.coeff k)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only; ring
  have hsplit : paperFT (polyShiftOp Q κ g) z =
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        Q.coeff k * paperFT (fun x => g (x - k * κ)) z := by
    unfold paperFT polyShiftOp
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    congr 1; funext u; ring
  rw [hsplit, eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [paperFT_comp_sub, ← Complex.exp_nat_mul]
  have e : ((k : ℝ) * κ : ℝ) = ((k * κ : ℝ) : ℂ) := rfl
  push_cast
  rw [show I * z * ((k : ℂ) * κ) = (k : ℂ) * (I * z * κ) by ring]
  ring

theorem hasDerivAt_polyShiftOp {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x) (Q : ℂ[X])
    (κ x : ℝ) : HasDerivAt (polyShiftOp Q κ g) (polyShiftOp Q κ g' x) x := by
  unfold polyShiftOp
  exact HasDerivAt.fun_sum fun k _ => ((hg (x - k * κ)).comp_sub_const x (k * κ)).const_mul _

theorem continuous_polyShiftOp {g : ℝ → ℂ} (hg : Continuous g) (Q : ℂ[X]) (κ : ℝ) :
    Continuous (polyShiftOp Q κ g) := by
  unfold polyShiftOp; fun_prop

theorem integral_norm_polyShiftOp_le {g : ℝ → ℂ} (hg : Integrable g) (Q : ℂ[X]) (κ : ℝ) :
    ∫ x, ‖polyShiftOp Q κ g x‖ ≤ coeffMass Q * ∫ x, ‖g x‖ := by
  have hi : ∀ k ∈ Finset.range (Q.natDegree + 1),
      Integrable (fun x => ‖Q.coeff k‖ * ‖g (x - k * κ)‖) :=
    fun k _ => (hg.comp_sub_right _).norm.const_mul _
  calc ∫ x, ‖polyShiftOp Q κ g x‖
      ≤ ∫ x, ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * ‖g (x - k * κ)‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_finsetSum _ hi) (Eventually.of_forall fun x => ?_)
        unfold polyShiftOp
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul]
    _ = coeffMass Q * ∫ x, ‖g x‖ := by
        rw [integral_finsetSum _ hi, coeffMass, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_sub_right_eq_self (fun x => ‖g x‖)]

theorem polyShiftOp_eq_zero {g : ℝ → ℂ} {b κ x : ℝ} (hκ : 0 ≤ κ) (Q : ℂ[X])
    (hg : ∀ u, b ≤ |u| → g u = 0) (hx : b + Q.natDegree * κ ≤ |x|) :
    polyShiftOp Q κ g x = 0 := by
  unfold polyShiftOp
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : (k : ℝ) ≤ Q.natDegree := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 0 ≤ k * κ := mul_nonneg hk0 hκ
  have h2 : k * κ ≤ Q.natDegree * κ := mul_le_mul_of_nonneg_right hk' hκ
  have hb : b ≤ |x - k * κ| := by
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hx
      exact le_trans (by linarith) (le_abs_self _)
    · rw [abs_of_neg hx0] at hx
      exact le_trans (by linarith) (neg_le_abs _)
  rw [hg _ hb, mul_zero]

end

end RHTower
