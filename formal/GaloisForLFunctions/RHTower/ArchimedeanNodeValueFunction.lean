import GaloisForLFunctions.RHTower.ArchimedeanUnitNodeEnergy

/-!
# The archimedean node value function is linear with gradient `Λ`

For a nonnegative finitely supported combination `c` of Weil tests write `A(c)` for its pole and
archimedean energy (`nodeArchEnergy`) and `L(c) = (L_n(c))_{n ≥ 2}` for its node vector
(`nodeVector`), the normalized symmetric values of the combined autocorrelation at `±log n`.
For a finitely supported vector `v` on the nodes let `nodeFibre v` be the set of energies `A(c)` of
the combinations `c` with `L(c) = v`, and `nodeValue v = inf nodeFibre v`.  A combination in the
fibre is blind at every node outside the support of `v` and carries the prescribed masses on it;
the fully blind cone is the fibre over `0`.

**Theorems.**
* `nodeFibre_nonempty`: every `v` is attained (pair tests at the nodes of `v`).
* `nodeValue_eq_vonMangoldtPairing`: under RH, `nodeValue v = Σ_n Λ(n) v_n` for every `v`.  The
  value function is linear, and its gradient is the von Mangoldt function.
* `not_bddBelow_nodeFibre`: if RH fails, every fibre is unbounded below.
* `riemannHypothesis_iff_bddBelow_nodeFibre`: RH holds iff one fibre is bounded below.
* `riemannHypothesis_iff_nodeFibre_add_neg_nonneg`: RH holds iff `A(c₊) + A(c₋) ≥ 0` whenever
  `L(c₊) = v` and `L(c₋) = −v`, for any single `v`.  At `v = e_m` this is a criterion at one node:
  the least energy carrying mass `+1` at `m` and the least energy carrying mass `−1` at `m` add up
  to `0` (under RH they are `Λ(m)` and `−Λ(m)`).

Proof of linearity.  Under RH the value function is finite, subadditive and positively
homogeneous, with `V(v) + V(−v) ≥ V(0) = 0`.  Fix `v₀ ≠ 0`.  The linear functional
`t v₀ ↦ t V(v₀)` on the line through `v₀` is dominated by `V`, so Hahn–Banach extends it to a
linear functional `g ≤ V` on all node vectors with `g(v₀) = V(v₀)`.  The weights `w(n) = g(e_n)`
satisfy `⟨w, L(f)⟩ = g(L(f)) ≤ V(L(f)) ≤ A(f)` for every single test `f`, so `w` is full-cone
Weil-positive and therefore equals `Λ` (`eq_vonMangoldt_of_weilPositiveFull`).  Hence
`V(v₀) = g(v₀) = ⟨Λ, v₀⟩`.
-/

open Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-- The energies of the nonnegative combinations with node vector `v`. -/
def nodeFibre (v : LogIndex →₀ ℝ) : Set ℝ :=
  {E | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ nodeVector c = v ∧ nodeArchEnergy c = E}

/-- The archimedean value function `V(v) = inf nodeFibre v`. -/
def nodeValue (v : LogIndex →₀ ℝ) : ℝ := sInf (nodeFibre v)

/-- The pairing `Σ_n Λ(n) v_n` of the von Mangoldt weights with a node vector. -/
def vonMangoldtPairing (v : LogIndex →₀ ℝ) : ℝ :=
  linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)) v

theorem nodeVector_eq (c : WeilTestFn →₀ ℝ) : nodeVector c = linearCombination ℝ logVector c := rfl

theorem nodeArchEnergy_eq (c : WeilTestFn →₀ ℝ) :
    nodeArchEnergy c =
      linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) c := rfl

theorem nodeVector_add (c d : WeilTestFn →₀ ℝ) : nodeVector (c + d) = nodeVector c + nodeVector d := by
  simp only [nodeVector_eq, map_add]

theorem nodeVector_smul (t : ℝ) (c : WeilTestFn →₀ ℝ) : nodeVector (t • c) = t • nodeVector c := by
  simp only [nodeVector_eq, map_smul]

theorem nodeArchEnergy_add (c d : WeilTestFn →₀ ℝ) :
    nodeArchEnergy (c + d) = nodeArchEnergy c + nodeArchEnergy d := by
  simp only [nodeArchEnergy_eq, map_add]

theorem nodeArchEnergy_smul (t : ℝ) (c : WeilTestFn →₀ ℝ) :
    nodeArchEnergy (t • c) = t * nodeArchEnergy c := by
  simp only [nodeArchEnergy_eq, map_smul, smul_eq_mul]

theorem nodeVector_single_test (f : WeilTestFn) : nodeVector (Finsupp.single f 1) = logVector f := by
  rw [nodeVector_eq, linearCombination_single, one_smul]

theorem nodeArchEnergy_single_test (f : WeilTestFn) :
    nodeArchEnergy (Finsupp.single f 1) = weilArchRe (EF.weilTest f.1 f.1) := by
  rw [nodeArchEnergy_eq, linearCombination_single, one_smul]

/-! ## Every node vector is attained -/

/-- A test with mass `−1` at the single node `m`. -/
def negUnitNodeTest (m : LogIndex) : WeilTestFn →₀ ℝ :=
  (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m)⁻¹ • Finsupp.single (pairTestFn m (-1)) 1

theorem nodeVector_negUnitNodeTest (m : LogIndex) :
    nodeVector (negUnitNodeTest m) = Finsupp.single m (-1) := by
  have ha := pairTest_weight_pos m
  rw [negUnitNodeTest, nodeVector_eq, map_smul, linearCombination_single, one_smul,
    logVector_pairTestFn, Finsupp.smul_single, smul_eq_mul]
  congr 1
  have e : 2 * (-1 : ℝ) * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m =
      -(2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) := by ring
  rw [e, mul_neg, inv_mul_cancel₀ ha.ne']

theorem negUnitNodeTest_nonneg (m : LogIndex) (f : WeilTestFn) : 0 ≤ negUnitNodeTest m f := by
  classical
  have ha := pairTest_weight_pos m
  rw [negUnitNodeTest, Finsupp.smul_apply, smul_eq_mul]
  refine mul_nonneg (inv_nonneg.mpr ha.le) ?_
  rw [Finsupp.single_apply]
  split_ifs <;> norm_num

/-- The canonical nonnegative combination with node vector `v`: scaled pair tests at the nodes of
`v`, with the sign of the prescribed mass. -/
def nodeLift (v : LogIndex →₀ ℝ) : WeilTestFn →₀ ℝ :=
  v.sum fun m t => if 0 ≤ t then t • unitNodeTest m else (-t) • negUnitNodeTest m

theorem nodeLift_nonneg (v : LogIndex →₀ ℝ) (f : WeilTestFn) : 0 ≤ nodeLift v f := by
  rw [nodeLift, Finsupp.sum_apply]
  refine Finsupp.sum_nonneg fun m _ => ?_
  split_ifs with h
  · rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg h (unitNodeTest_nonneg m f)
  · rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith) (negUnitNodeTest_nonneg m f)

theorem nodeVector_nodeLift (v : LogIndex →₀ ℝ) : nodeVector (nodeLift v) = v := by
  rw [nodeLift, nodeVector_eq, map_finsuppSum]
  conv_rhs => rw [← Finsupp.sum_single v]
  refine Finsupp.sum_congr fun m _ => ?_
  split_ifs with h
  · rw [map_smul, ← nodeVector_eq, nodeVector_unitNodeTest, Finsupp.smul_single, smul_eq_mul,
      mul_one]
  · rw [map_smul, ← nodeVector_eq, nodeVector_negUnitNodeTest, Finsupp.smul_single, smul_eq_mul,
      mul_neg, mul_one, neg_neg]

theorem nodeArchEnergy_nodeLift_mem (v : LogIndex →₀ ℝ) : nodeArchEnergy (nodeLift v) ∈ nodeFibre v :=
  ⟨nodeLift v, nodeLift_nonneg v, nodeVector_nodeLift v, rfl⟩

/-- **Every node vector is attained.** -/
theorem nodeFibre_nonempty (v : LogIndex →₀ ℝ) : (nodeFibre v).Nonempty :=
  ⟨_, nodeArchEnergy_nodeLift_mem v⟩

theorem zero_mem_nodeFibre_zero : (0 : ℝ) ∈ nodeFibre 0 :=
  ⟨0, fun _ => le_rfl, by simp [nodeVector_eq], by simp [nodeArchEnergy_eq]⟩

theorem weilArchRe_mem_nodeFibre (f : WeilTestFn) :
    weilArchRe (EF.weilTest f.1 f.1) ∈ nodeFibre (logVector f) :=
  ⟨Finsupp.single f 1, fun g => by
      classical
      rw [Finsupp.single_apply]; split_ifs <;> norm_num,
    nodeVector_single_test f, nodeArchEnergy_single_test f⟩

/-! ## The fibres form a convex cone -/

theorem add_mem_nodeFibre {v w : LogIndex →₀ ℝ} {E F : ℝ} (hE : E ∈ nodeFibre v)
    (hF : F ∈ nodeFibre w) : E + F ∈ nodeFibre (v + w) := by
  obtain ⟨c, hc, hcv, rfl⟩ := hE
  obtain ⟨d, hd, hdw, rfl⟩ := hF
  refine ⟨c + d, fun f => ?_, ?_, ?_⟩
  · rw [Finsupp.add_apply]; exact add_nonneg (hc f) (hd f)
  · rw [nodeVector_add, hcv, hdw]
  · rw [nodeArchEnergy_add]

theorem smul_mem_nodeFibre {v : LogIndex →₀ ℝ} {E t : ℝ} (ht : 0 ≤ t) (hE : E ∈ nodeFibre v) :
    t * E ∈ nodeFibre (t • v) := by
  obtain ⟨c, hc, hcv, rfl⟩ := hE
  refine ⟨t • c, fun f => ?_, ?_, ?_⟩
  · rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg ht (hc f)
  · rw [nodeVector_smul, hcv]
  · rw [nodeArchEnergy_smul]

theorem nodeFibre_smul {v : LogIndex →₀ ℝ} {t : ℝ} (ht : 0 < t) :
    nodeFibre (t • v) = (fun E => t * E) '' nodeFibre v := by
  ext E
  constructor
  · intro hE
    refine ⟨t⁻¹ * E, ?_, by simp only; rw [mul_inv_cancel_left₀ ht.ne']⟩
    have := smul_mem_nodeFibre (inv_nonneg.mpr ht.le) hE
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
  · rintro ⟨F, hF, rfl⟩
    exact smul_mem_nodeFibre ht.le hF

/-! ## Under RH the value function is finite and sublinear -/

/-- Under RH every energy in the fibre over `v` is at least `⟨Λ, v⟩` (Weil positivity). -/
theorem vonMangoldtPairing_le_of_mem_nodeFibre (hRH : RiemannHypothesis) {v : LogIndex →₀ ℝ}
    {E : ℝ} (hE : E ∈ nodeFibre v) : vonMangoldtPairing v ≤ E := by
  obtain ⟨c, hc, hcv, rfl⟩ := hE
  have h1 := sum_nonneg_of_weilPositiveFull
    (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc
  rw [sum_re_weilFullFunctional] at h1
  change 0 ≤ nodeArchEnergy c - vonMangoldtPairing (nodeVector c) at h1
  rw [hcv] at h1
  linarith

theorem bddBelow_nodeFibre (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) :
    BddBelow (nodeFibre v) :=
  ⟨vonMangoldtPairing v, fun _ hE => vonMangoldtPairing_le_of_mem_nodeFibre hRH hE⟩

theorem vonMangoldtPairing_le_nodeValue (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) :
    vonMangoldtPairing v ≤ nodeValue v :=
  le_csInf (nodeFibre_nonempty v) fun _ hE => vonMangoldtPairing_le_of_mem_nodeFibre hRH hE

theorem nodeValue_le_of_mem (hRH : RiemannHypothesis) {v : LogIndex →₀ ℝ} {E : ℝ}
    (hE : E ∈ nodeFibre v) : nodeValue v ≤ E :=
  csInf_le (bddBelow_nodeFibre hRH v) hE

theorem nodeValue_zero (hRH : RiemannHypothesis) : nodeValue 0 = 0 := by
  refine le_antisymm (nodeValue_le_of_mem hRH zero_mem_nodeFibre_zero) ?_
  have := vonMangoldtPairing_le_nodeValue hRH 0
  rwa [vonMangoldtPairing, map_zero] at this

theorem nodeValue_add_le (hRH : RiemannHypothesis) (v w : LogIndex →₀ ℝ) :
    nodeValue (v + w) ≤ nodeValue v + nodeValue w := by
  have h : ∀ E ∈ nodeFibre v, ∀ F ∈ nodeFibre w, nodeValue (v + w) ≤ E + F :=
    fun E hE F hF => nodeValue_le_of_mem hRH (add_mem_nodeFibre hE hF)
  have h1 : ∀ F ∈ nodeFibre w, nodeValue (v + w) - F ≤ nodeValue v := fun F hF =>
    le_csInf (nodeFibre_nonempty v) fun E hE => by linarith [h E hE F hF]
  have h2 : nodeValue (v + w) - nodeValue v ≤ nodeValue w :=
    le_csInf (nodeFibre_nonempty w) fun F hF => by linarith [h1 F hF]
  linarith

theorem nodeValue_smul (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t) (v : LogIndex →₀ ℝ) :
    nodeValue (t • v) = t * nodeValue v := by
  rw [nodeValue, nodeValue, nodeFibre_smul ht]
  have hne := nodeFibre_nonempty v
  have hbdd := bddBelow_nodeFibre hRH v
  have hbdd' : BddBelow ((fun E => t * E) '' nodeFibre v) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨t * b, by rintro _ ⟨E, hE, rfl⟩; exact mul_le_mul_of_nonneg_left (hb hE) ht.le⟩
  refine le_antisymm ?_ ?_
  · have h1 : ∀ E ∈ nodeFibre v, sInf ((fun E => t * E) '' nodeFibre v) ≤ t * E :=
      fun E hE => csInf_le hbdd' ⟨E, hE, rfl⟩
    have h2 : t⁻¹ * sInf ((fun E => t * E) '' nodeFibre v) ≤ sInf (nodeFibre v) := by
      refine le_csInf hne fun E hE => ?_
      rw [inv_mul_le_iff₀ ht]
      exact h1 E hE
    have := mul_le_mul_of_nonneg_left h2 ht.le
    rwa [mul_inv_cancel_left₀ ht.ne'] at this
  · refine le_csInf (s := (fun E => t * E) '' nodeFibre v) (hne.image _) ?_
    rintro _ ⟨E, hE, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd hE) ht.le

theorem nodeValue_add_neg_nonneg (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) :
    0 ≤ nodeValue v + nodeValue (-v) := by
  have := nodeValue_add_le hRH v (-v)
  rwa [add_neg_cancel, nodeValue_zero hRH] at this

/-- Positive homogeneity in both directions: `t V(v₀) ≤ V(t v₀)` for every real `t`. -/
theorem mul_nodeValue_le_nodeValue_smul (hRH : RiemannHypothesis) (t : ℝ) (v : LogIndex →₀ ℝ) :
    t * nodeValue v ≤ nodeValue (t • v) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have e : t • v = (-t) • (-v) := by rw [smul_neg, neg_smul, neg_neg]
    rw [e, nodeValue_smul hRH (by linarith) (-v)]
    have := nodeValue_add_neg_nonneg hRH v
    nlinarith
  · rw [zero_smul, nodeValue_zero hRH, zero_mul]
  · rw [nodeValue_smul hRH ht]

/-! ## Linearity: Hahn–Banach and cone uniqueness -/

/-- A linear functional on node vectors is the pairing with its values at the unit vectors. -/
theorem linearMap_eq_linearCombination (g : (LogIndex →₀ ℝ) →ₗ[ℝ] ℝ) :
    g = linearCombination ℝ fun j : LogIndex => g (Finsupp.single j 1) := by
  refine Finsupp.lhom_ext fun a b => ?_
  rw [linearCombination_single, ← Finsupp.smul_single_one a b, map_smul]

/-- A linear functional dominated by the value function is a full-cone Weil-positive weight, hence
equals the von Mangoldt pairing. -/
theorem linearMap_eq_vonMangoldtPairing_of_le (hRH : RiemannHypothesis)
    (g : (LogIndex →₀ ℝ) →ₗ[ℝ] ℝ) (hg : ∀ v, g v ≤ nodeValue v) (v : LogIndex →₀ ℝ) :
    g v = vonMangoldtPairing v := by
  set lam : LogIndex → ℝ := fun j => g (Finsupp.single j 1) with hlam
  have hle : ∀ f : WeilTestFn,
      linearCombination ℝ lam (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := by
    intro f
    rw [hlam, ← linearMap_eq_linearCombination g]
    exact (hg _).trans (nodeValue_le_of_mem hRH (weilArchRe_mem_nodeFibre f))
  have hW := weilPositiveFull_of_le_arch hle
  have hΛ := RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW
  have hlamΛ : lam = fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ) := by
    funext j
    have := hΛ j j.2
    simpa [j.2] using this
  rw [linearMap_eq_linearCombination g, ← hlam, hlamΛ]
  rfl

/-- **The archimedean value function is linear with gradient `Λ`.**  Under RH,
`inf {A(c) : c ≥ 0, L(c) = v} = Σ_n Λ(n) v_n` for every finitely supported node vector `v`. -/
theorem nodeValue_eq_vonMangoldtPairing (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) :
    nodeValue v = vonMangoldtPairing v := by
  by_cases hv : v = 0
  · subst hv
    rw [nodeValue_zero hRH, vonMangoldtPairing, map_zero]
  -- the linear functional `t v ↦ t V(v)` on the line through `v`
  have H : ∀ c : ℝ, c • v = 0 → (RingHom.id ℝ) c • nodeValue v = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · exact absurd h hv
  have hdom : ∀ x : (LinearPMap.mkSpanSingleton' v (nodeValue v) H).domain,
      LinearPMap.mkSpanSingleton' v (nodeValue v) H x ≤ nodeValue x := by
    intro x
    have hx : (x : LogIndex →₀ ℝ) ∈ Submodule.span ℝ {v} := x.2
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    have hx' : x = ⟨a • v, by rw [ha]; exact x.2⟩ := Subtype.ext ha.symm
    rw [hx', LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    exact mul_nodeValue_le_nodeValue_smul hRH a v
  obtain ⟨g, hgφ, hg⟩ := exists_extension_of_le_sublinear
    (LinearPMap.mkSpanSingleton' v (nodeValue v) H) nodeValue
    (fun c hc x => nodeValue_smul hRH hc x) (nodeValue_add_le hRH) hdom
  have hgv : g v = nodeValue v := by
    have hmem : v ∈ (LinearPMap.mkSpanSingleton' v (nodeValue v) H).domain :=
      Submodule.mem_span_singleton_self v
    have := hgφ ⟨v, hmem⟩
    rw [this, LinearPMap.mkSpanSingleton'_apply_self]
  rw [← hgv]
  exact linearMap_eq_vonMangoldtPairing_of_le hRH g hg v

/-- Under RH, mass `t` at the single node `m` costs exactly `t Λ(m)`: `+Λ(m)` for unit positive
mass and `−Λ(m)` for unit negative mass at a prime power, and nothing at the other integers. -/
theorem nodeValue_single (hRH : RiemannHypothesis) (m : LogIndex) (t : ℝ) :
    nodeValue (Finsupp.single m t) = t * ArithmeticFunction.vonMangoldt (m : ℕ) := by
  rw [nodeValue_eq_vonMangoldtPairing hRH, vonMangoldtPairing, linearCombination_single,
    smul_eq_mul]

/-- Under RH the value function is odd: `V(v) + V(−v) = 0`. -/
theorem nodeValue_add_neg_eq_zero (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) :
    nodeValue v + nodeValue (-v) = 0 := by
  rw [nodeValue_eq_vonMangoldtPairing hRH, nodeValue_eq_vonMangoldtPairing hRH,
    vonMangoldtPairing, vonMangoldtPairing, map_neg, add_neg_cancel]

/-! ## Without RH every fibre is unbounded below -/

/-- **If RH fails, every fibre is unbounded below.** -/
theorem not_bddBelow_nodeFibre (hRH : ¬ RiemannHypothesis) (v : LogIndex →₀ ℝ) :
    ¬ BddBelow (nodeFibre v) := by
  have hP : ¬ PrimeBlindPositive := fun h =>
    hRH (riemannHypothesis_iff_primeBlindPositive_unconditional.mpr h)
  simp only [PrimeBlindPositive, not_forall, not_le, exists_prop] at hP
  obtain ⟨c₀, hc₀, hnull, hneg⟩ := hP
  rw [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at hneg
  have hv₀ : nodeVector c₀ = 0 := linearCombination_logVector_eq_zero hnull
  rw [not_bddBelow_iff]
  intro x
  set t : ℝ := (|nodeArchEnergy (nodeLift v)| + |x| + 1) / (-nodeArchEnergy c₀) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  refine ⟨nodeArchEnergy (nodeLift v + t • c₀), ⟨nodeLift v + t • c₀, fun f => ?_, ?_, rfl⟩, ?_⟩
  · rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (nodeLift_nonneg v f) (mul_nonneg ht0 (hc₀ f))
  · rw [nodeVector_add, nodeVector_smul, nodeVector_nodeLift, hv₀, smul_zero, add_zero]
  · rw [nodeArchEnergy_add, nodeArchEnergy_smul]
    have h2 : t * nodeArchEnergy c₀ = -(|nodeArchEnergy (nodeLift v)| + |x| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith : -nodeArchEnergy c₀ ≠ 0)]
      ring
    have h3 := le_abs_self (nodeArchEnergy (nodeLift v))
    have h4 := neg_abs_le x
    linarith

/-- **RH is the boundedness of a single fibre.** -/
theorem riemannHypothesis_iff_bddBelow_nodeFibre (v : LogIndex →₀ ℝ) :
    RiemannHypothesis ↔ BddBelow (nodeFibre v) :=
  ⟨fun h => bddBelow_nodeFibre h v, fun h => by
    by_contra hRH
    exact not_bddBelow_nodeFibre hRH v h⟩

/-- **The two-sided criterion at one node vector.**  RH holds iff, for a single `v`, the energies
of the combinations carrying mass `v` and those carrying mass `−v` always add up to a nonnegative
number: `A(c₊) + A(c₋) ≥ 0` whenever `L(c₊) = v` and `L(c₋) = −v`. -/
theorem riemannHypothesis_iff_nodeFibre_add_neg_nonneg (v : LogIndex →₀ ℝ) :
    RiemannHypothesis ↔ ∀ E ∈ nodeFibre v, ∀ F ∈ nodeFibre (-v), 0 ≤ E + F := by
  constructor
  · intro hRH E hE F hF
    have h1 := vonMangoldtPairing_le_of_mem_nodeFibre hRH hE
    have h2 := vonMangoldtPairing_le_of_mem_nodeFibre hRH hF
    rw [vonMangoldtPairing, map_neg, ← vonMangoldtPairing] at h2
    linarith
  · intro h
    refine riemannHypothesis_iff_primeBlindPositive_unconditional.mpr fun c hc hnull => ?_
    rw [sum_weilArchRe_eq, ← nodeArchEnergy_eq]
    have hv₀ : nodeVector c = 0 := linearCombination_logVector_eq_zero hnull
    by_contra hneg
    rw [not_le] at hneg
    set t : ℝ := (|nodeArchEnergy (nodeLift v)| + |nodeArchEnergy (nodeLift (-v))| + 1) /
      (-nodeArchEnergy c) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hE : nodeArchEnergy (t • c + nodeLift v) ∈ nodeFibre v := by
      refine ⟨t • c + nodeLift v, fun f => ?_, ?_, rfl⟩
      · rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ht0 (hc f)) (nodeLift_nonneg v f)
      · rw [nodeVector_add, nodeVector_smul, nodeVector_nodeLift, hv₀, smul_zero, zero_add]
    have h1 := h _ hE _ (nodeArchEnergy_nodeLift_mem (-v))
    rw [nodeArchEnergy_add, nodeArchEnergy_smul] at h1
    have h2 : t * nodeArchEnergy c =
        -(|nodeArchEnergy (nodeLift v)| + |nodeArchEnergy (nodeLift (-v))| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith : -nodeArchEnergy c ≠ 0)]
      ring
    have h3 := le_abs_self (nodeArchEnergy (nodeLift v))
    have h4 := le_abs_self (nodeArchEnergy (nodeLift (-v)))
    linarith

/-- **RH at a single node.**  For any node `m ≥ 2`, RH holds iff every combination carrying unit
mass at `m` and every combination carrying unit negative mass at `m`, both blind elsewhere, have
energies adding up to a nonnegative number. -/
theorem riemannHypothesis_iff_unitNode_two_sided (m : LogIndex) :
    RiemannHypothesis ↔
      ∀ E ∈ nodeFibre (Finsupp.single m 1), ∀ F ∈ nodeFibre (Finsupp.single m (-1)), 0 ≤ E + F := by
  rw [riemannHypothesis_iff_nodeFibre_add_neg_nonneg (Finsupp.single m 1)]
  simp only [Finsupp.single_neg]

end

end RHTower.WeilOneSided
