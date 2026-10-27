import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCoupledSurvivalLaw
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheRamanujanTwinsSurviveExactlyOnPerOrderRelations

/-!
# The archimedean place pays the arithmetic point

The coupled survival law (`TheCoupledSurvivalLaw`) says that a partner whose counterterm has rank
one pays at most one prime direction, and pays it exactly when the coupling is matched (`|b| = 1`).
This file computes the coupling between the two places in the periodic class of RBG and finds the
matched direction: the arithmetic point.

The **joint germ** places the torsion orbits `O_n`, `n ∈ S`, with their normalized Ramanujan modes
`c_n(k)/√φ(n)`, and `k` archimedean nodes with the constant mode `1` (the lattice germ), each at a
nonnegative node; its Abel levels are Cauchy forms (`jointGerm_quad_nonneg`), and its counterterm is
the Cesàro Gram of the joint modes (`tendsto_jointGerm`).

* **Ramanujan orthogonality** (`ramanujanMode_one`, `periodMean_jointMode`): `c_1 = 1`, and
  `mean(c_m c_n) = φ(n) δ_{mn}` over a common period. The Ramanujan mode of an orbit of order
  `n ≥ 2` has mean zero: it is Cesàro orthogonal to the archimedean mode.
* **The joint counterterm is the matched rank-one coupling** (`jointGram_eq`): it is
  `[[1, e₁ 𝟙ᵀ], [𝟙 e₁ᵀ, 𝟙𝟙ᵀ]]`, with `e₁` the arithmetic point `O_1`. The coupling vector `e₁` has
  norm one: the arithmetic point is matched to the archimedean place.
* **The archimedean place pays exactly the arithmetic point** (`primeSurvival_jointGram`): the prime
  survival of the joint germ is `ℝ e₁` if `1 ∈ S` and `0` otherwise; no orbit of order `≥ 2`
  survives, however many archimedean nodes are added.
* **Survival** (`jointGerm_survival`): the renormalized limit is nonnegative on `(−s e₁, w)` whenever
  the archimedean coefficients sum to `s` — the matched cancellation of the archimedean divergence by
  the pole node (RBG `harmonicKernel_nonneg`), now as an instance of the coupled law.

So in the periodic class the two places couple at one point. The arithmetic point is the unique
torsion orbit whose mode is not Cesàro orthogonal to the archimedean mode, because `O_1 = {1}` is the
fixed point of every power map and `c_1 ≡ 1` is the constant mode itself.
-/

noncomputable section

open Filter Topology Finset Matrix

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open RenormalizedBiarithmeticGeometry

variable {S : Finset ℕ} {k : ℕ}

/-! ### Ramanujan orthogonality -/

/-- The Ramanujan mode of the arithmetic point is the constant mode: `c_1 ≡ 1`. -/
theorem ramanujanMode_one (j : ℕ) : ramanujanMode 1 j = 1 := by
  simp [ramanujanMode, ArithmeticEffectivityTheory.ramanujanSum]

/-- The **joint modes**: `c_n/√φ(n)` on the orbit `O_n`, the constant `1` on an archimedean node. -/
def jointMode (S : Finset ℕ) (k : ℕ) : S ⊕ Fin k → ℕ → ℝ
  | Sum.inl n => fun j => ramanujanMode n j / Real.sqrt (Nat.totient n)
  | Sum.inr _ => fun _ => 1

/-- The **joint Cesàro Gram** over the period `q`. -/
def jointGram (S : Finset ℕ) (k q : ℕ) : Matrix (S ⊕ Fin k) (S ⊕ Fin k) ℝ :=
  Matrix.of fun α β => periodMean (fun j => jointMode S k α j * jointMode S k β j) q

/-- The arithmetic point `e₁ ∈ ℝ^S`. -/
def arithmeticPoint (S : Finset ℕ) : S → ℝ := fun n => if (n : ℕ) = 1 then 1 else 0

theorem periodMean_ramanujanMode_mul {m n q : ℕ} (hm : 0 < m) (hn : 0 < n) (hmq : m ∣ q)
    (hnq : n ∣ q) (hq : 0 < q) :
    periodMean (fun j => ramanujanMode m j * ramanujanMode n j) q =
      if m = n then (Nat.totient n : ℝ) else 0 := by
  rw [periodMean, sum_ramanujanMode_mul hm hn hmq hnq]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  split_ifs
  · field_simp
  · simp

/-- **The joint counterterm is the matched rank-one coupling**: for a common period `q` of the
orders, `jointGram = [[1, e₁ 𝟙ᵀ], [𝟙 e₁ᵀ, 𝟙𝟙ᵀ]]`. -/
theorem jointGram_eq (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (hq : 0 < q) (hdvd : ∀ n ∈ S, n ∣ q) :
    jointGram S k q = coupled 1 (vecMulVec (arithmeticPoint S) (fun _ => 1))
      (vecMulVec (fun _ => 1) (fun _ => 1)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  ext (m | j) (n | j')
  · -- prime block: normalized Ramanujan orthogonality
    have hm := hS m m.2
    have hn := hS n n.2
    have h := periodMean_ramanujanMode_mul hm hn (hdvd m m.2) (hdvd n n.2) hq
    have hφ : (0 : ℝ) < Nat.totient (n : ℕ) := by exact_mod_cast Nat.totient_pos.mpr hn
    simp only [jointGram, jointMode, coupled, of_apply, fromBlocks_apply₁₁, one_apply]
    have hfac : periodMean (fun j => ramanujanMode m j / Real.sqrt (Nat.totient (m : ℕ)) *
        (ramanujanMode n j / Real.sqrt (Nat.totient (n : ℕ)))) q =
        periodMean (fun j => ramanujanMode m j * ramanujanMode n j) q /
          (Real.sqrt (Nat.totient (m : ℕ)) * Real.sqrt (Nat.totient (n : ℕ))) := by
      have hsm : Real.sqrt (Nat.totient (m : ℕ)) ≠ 0 :=
        (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm)).ne'
      have hsn : Real.sqrt (Nat.totient (n : ℕ)) ≠ 0 := (Real.sqrt_pos.mpr hφ).ne'
      simp only [periodMean, sum_div]
      refine sum_congr rfl fun j _ => ?_
      field_simp
    rw [hfac, h]
    by_cases hmn : (m : ℕ) = n
    · have hmn' : m = n := Subtype.ext hmn
      subst hmn'
      rw [if_pos rfl, if_pos rfl, ← Real.sqrt_mul hφ.le, Real.sqrt_mul_self hφ.le, div_self hφ.ne']
    · rw [if_neg hmn, if_neg (fun h => hmn (congrArg Subtype.val h)), zero_div]
  · -- coupling: the mean of `c_n` is `δ_{n,1}`
    have hn := hS m m.2
    have h := periodMean_ramanujanMode_mul one_pos hn (one_dvd q) (hdvd m m.2) hq
    simp only [ramanujanMode_one, one_mul] at h
    simp only [jointGram, jointMode, coupled, of_apply, fromBlocks_apply₁₂, vecMulVec_apply,
      arithmeticPoint, mul_one]
    have hfac : periodMean (fun j => ramanujanMode m j / Real.sqrt (Nat.totient (m : ℕ))) q =
        periodMean (fun j => ramanujanMode m j) q / Real.sqrt (Nat.totient (m : ℕ)) := by
      simp only [periodMean, sum_div]
      exact sum_congr rfl fun j _ => div_right_comm _ _ _
    rw [hfac, h]
    by_cases h1 : (m : ℕ) = 1
    · simp [h1]
    · simp [h1, Ne.symm h1]
  · -- the transposed coupling
    have hn := hS n n.2
    have h := periodMean_ramanujanMode_mul one_pos hn (one_dvd q) (hdvd n n.2) hq
    simp only [ramanujanMode_one, one_mul] at h
    simp only [jointGram, jointMode, coupled, of_apply, fromBlocks_apply₂₁, transpose_apply,
      vecMulVec_apply, arithmeticPoint, one_mul]
    have hfac : periodMean (fun j => ramanujanMode n j / Real.sqrt (Nat.totient (n : ℕ))) q =
        periodMean (fun j => ramanujanMode n j) q / Real.sqrt (Nat.totient (n : ℕ)) := by
      simp only [periodMean, sum_div]
      exact sum_congr rfl fun j _ => div_right_comm _ _ _
    rw [hfac, h]
    by_cases h1 : (n : ℕ) = 1
    · simp [h1]
    · simp [h1, Ne.symm h1]
  · -- partner block: the archimedean mode has mean one
    simp only [jointGram, jointMode, coupled, of_apply, fromBlocks_apply₂₂, vecMulVec_apply,
      mul_one, periodMean, sum_const, card_range, nsmul_eq_mul]
    field_simp

theorem card_filter_val_eq_one (S : Finset ℕ) :
    ((univ : Finset S).filter fun n : S => (n : ℕ) = 1).card = if 1 ∈ S then 1 else 0 := by
  split_ifs with h1
  · rw [card_eq_one]
    exact ⟨⟨1, h1⟩, by ext n; simp [Subtype.ext_iff]⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro n _ hn
    exact h1 (hn ▸ n.2)

/-- The arithmetic point has norm one when it is an order of `S`. -/
theorem dotProduct_arithmeticPoint_self (S : Finset ℕ) :
    arithmeticPoint S ⬝ᵥ arithmeticPoint S = if 1 ∈ S then 1 else 0 := by
  have h : ∀ n : S, arithmeticPoint S n * arithmeticPoint S n =
      if (n : ℕ) = 1 then 1 else 0 := fun n => by
    unfold arithmeticPoint; split_ifs <;> norm_num
  rw [dotProduct, sum_congr rfl fun n _ => h n, sum_boole, card_filter_val_eq_one]
  split_ifs <;> simp

/-- **The archimedean place pays exactly the arithmetic point.** The prime survival of the joint
counterterm is the line of the arithmetic point if `1 ∈ S`, and `0` otherwise. -/
theorem primeSurvival_jointGram (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (hq : 0 < q)
    (hdvd : ∀ n ∈ S, n ∣ q) (hk : 0 < k) :
    (LinearMap.ker (jointGram S k q).mulVecLin).map (LinearMap.funLeft ℝ ℝ Sum.inl) =
      if 1 ∈ S then Submodule.span ℝ {arithmeticPoint S} else ⊥ := by
  classical
  rw [jointGram_eq hS hq hdvd]
  show primeSurvival _ _ _ = _
  have hv : (fun _ : Fin k => (1 : ℝ)) ≠ 0 := fun h => by
    simpa using congrFun h ⟨0, hk⟩
  rw [primeSurvival_rankOne hv]
  have hnorm := dotProduct_arithmeticPoint_self S
  split_ifs with h1 h2 h2
  · rfl
  · rw [hnorm, if_neg h2] at h1; exact absurd h1 zero_ne_one
  · rw [hnorm, if_pos h2] at h1; exact absurd rfl h1
  · rfl

/-! ### The joint germ as a positive regularized family -/

/-- The **joint germ** at nonnegative nodes `x`: the twisted Abel germ of the joint modes. -/
def jointGerm (S : Finset ℕ) (k : ℕ) (x : S ⊕ Fin k → ℝ) (r : ℝ) :
    Matrix (S ⊕ Fin k) (S ⊕ Fin k) ℝ :=
  Matrix.of fun α β => twistedGerm (fun j => jointMode S k α j * jointMode S k β j) r
    (1 + x α + x β)

theorem jointMode_periodic (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (hdvd : ∀ n ∈ S, n ∣ q)
    (α : S ⊕ Fin k) : Function.Periodic (jointMode S k α) q := by
  rcases α with n | j
  · intro i
    obtain ⟨c, hc⟩ := hdvd n n.2
    have h := (ramanujanMode_periodic (hS n n.2)).nat_mul c
    have h' : Function.Periodic (ramanujanMode n) q := by
      rw [hc, mul_comm]; simpa only [Nat.cast_id] using h
    simp only [jointMode]
    rw [h' i]
  · intro i; rfl

/-- **The joint germ is positive** at every radius `0 ≤ r < 1`: reindexed, it is a periodic germ of
RBG, whose Abel levels are Cauchy forms. -/
theorem jointGerm_quad_nonneg (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (hq : 0 < q)
    (hdvd : ∀ n ∈ S, n ∣ q) {x : S ⊕ Fin k → ℝ} (hx : ∀ α, 0 ≤ x α) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (C : S ⊕ Fin k → ℝ) : 0 ≤ quad (jointGerm S k x r) C := by
  set e := Fintype.equivFin (S ⊕ Fin k)
  have h := periodicGerm_quad_nonneg (fun i => jointMode S k (e.symm i)) hq
    (fun i => jointMode_periodic hS hdvd (e.symm i)) (x := fun i => x (e.symm i))
    (fun i => hx _) hr0 hr1 (fun i => C (e.symm i))
  have heq : quad (periodicGerm (fun i => jointMode S k (e.symm i)) (fun i => x (e.symm i)) r)
      (fun i => C (e.symm i)) = quad (jointGerm S k x r) C := by
    simp only [quad, periodicGerm, jointGerm, of_apply]
    exact Fintype.sum_equiv e.symm _ _ fun i => Fintype.sum_equiv e.symm _ _ fun j => rfl
  rwa [heq] at h

/-- **The joint germ is a regularized family with the joint Cesàro Gram as counterterm.** -/
theorem tendsto_jointGerm (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (hq : 0 < q) (hdvd : ∀ n ∈ S, n ∣ q)
    {x : S ⊕ Fin k → ℝ} (hx : ∀ α, 0 ≤ x α) :
    ∃ A : Matrix (S ⊕ Fin k) (S ⊕ Fin k) ℝ, ∀ α β,
      Tendsto (fun r => jointGerm S k x r α β - (-Real.log (1 - r)) * jointGram S k q α β)
        (𝓝[<] 1) (𝓝 (A α β)) := by
  have hlim : ∀ α β, ∃ L : ℝ, Tendsto (fun r => jointGerm S k x r α β -
      (-Real.log (1 - r)) * jointGram S k q α β) (𝓝[<] 1) (𝓝 L) := by
    intro α β
    have hprod : Function.Periodic (fun j => jointMode S k α j * jointMode S k β j) q :=
      fun j => by simp only [jointMode_periodic hS hdvd α j, jointMode_periodic hS hdvd β j]
    obtain ⟨L, hL⟩ := tendsto_twistedGerm_add_mean_log hq hprod
      (show 0 < 1 + x α + x β by linarith [hx α, hx β])
    exact ⟨L, hL.congr fun r => by simp only [jointGerm, jointGram, of_apply]; ring⟩
  choose A hA using hlim
  exact ⟨Matrix.of A, fun α β => hA α β⟩

/-- **The matched survival of the joint germ.** If the arithmetic point is among the orders, the
renormalized limit of the joint germ is nonnegative on `(−s e₁, w)` whenever the archimedean
coefficients `w` sum to `s`; and the prime part of every survival vector is the multiple
`−(Σ w) e₁` of the arithmetic point. -/
theorem jointGerm_survival (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (hq : 0 < q) (hdvd : ∀ n ∈ S, n ∣ q)
    {x : S ⊕ Fin k → ℝ} (hx : ∀ α, 0 ≤ x α) :
    ∃ A : Matrix (S ⊕ Fin k) (S ⊕ Fin k) ℝ,
      (∀ α β, Tendsto (fun r => jointGerm S k x r α β - (-Real.log (1 - r)) * jointGram S k q α β)
        (𝓝[<] 1) (𝓝 (A α β))) ∧
      (1 ∈ S → ∀ (s : ℝ) (w : Fin k → ℝ), ∑ j, w j = s →
        0 ≤ quad A (Sum.elim (-s • arithmeticPoint S) w)) ∧
      ∀ (u : S → ℝ) (w : Fin k → ℝ), Sum.elim u w ∈ survivalCone (jointGram S k q) →
        u = -(∑ j, w j) • arithmeticPoint S := by
  classical
  obtain ⟨A, hA⟩ := tendsto_jointGerm hS hq hdvd hx
  have hQ : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ C, 0 ≤ quad (jointGerm S k x r) C := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr C
    exact jointGerm_quad_nonneg hS hq hdvd hx hr.1.le hr.2 C
  have hpos0 : ∀ C, 0 ≤ quad (jointGram S k q) C :=
    counterterm_nonneg hQ tendsto_neg_log_one_sub hA
  have hker : ∀ (u : S → ℝ) (w : Fin k → ℝ), Sum.elim u w ∈ survivalCone (jointGram S k q) ↔
      u = -(∑ j, w j) • arithmeticPoint S ∧ arithmeticPoint S ⬝ᵥ u + ∑ j, w j = 0 := by
    intro u w
    have hpos := hpos0
    rw [jointGram_eq hS hq hdvd] at hpos ⊢
    have hDs : (vecMulVec (fun _ : Fin k => (1 : ℝ)) (fun _ => 1)).IsSymm := by
      unfold Matrix.IsSymm; rw [transpose_vecMulVec]
    rw [mem_survivalCone_coupled_iff isSymm_one hDs hpos, transpose_vecMulVec,
      vecMulVec_mulVec', vecMulVec_mulVec', vecMulVec_mulVec', one_mulVec, ← add_smul]
    have hsum : ∀ w : Fin k → ℝ, (fun _ : Fin k => (1 : ℝ)) ⬝ᵥ w = ∑ j, w j := fun w => by
      simp [dotProduct]
    rw [hsum]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h1, ?_⟩
      by_cases hk : k = 0
      · subst hk
        have hu : u = 0 := by
          have := h1; simpa using this
        simp [hu]
      · have := congrFun h2 ⟨0, Nat.pos_of_ne_zero hk⟩
        simpa using this
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, neg_smul, neg_add_cancel], by rw [h2, zero_smul]⟩
  refine ⟨A, hA, fun h1 s w hw => ?_, fun u w hu => ((hker u w).mp hu).1⟩
  refine quad_nonneg_of_regularized hQ hA ((hker _ w).mpr ⟨by rw [hw], ?_⟩)
  have hnorm : arithmeticPoint S ⬝ᵥ arithmeticPoint S = 1 := by
    rw [dotProduct_arithmeticPoint_self, if_pos h1]
  rw [dotProduct_smul, hnorm, smul_eq_mul, hw]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
