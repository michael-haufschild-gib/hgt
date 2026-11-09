import GaloisForLFunctions.HTGeometry.KleinbockMargulis.SmoothGoodOne

/-!
# Finite covers of derivative sublevel sets

A nonvanishing derivative of order `k` prevents `k+1` widely separated small values.
Lagrange interpolation bounds their separation, and a maximal separated finite subset then
covers the entire sublevel set by at most `k` short intervals.
-/

open Set Polynomial

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

open HTGeometry.KleinbockMargulis

/-- The radius factor for a cover of a sublevel set controlled by its `k`-th derivative. -/
def derivativeCoverConstant (k : ℕ) (A : ℝ) : ℝ :=
  2 * (((k + 1).factorial : ℝ) / A) ^ ((k : ℝ)⁻¹)

theorem derivativeCoverConstant_pos (k : ℕ) {A : ℝ} (hA : 0 < A) :
    0 < derivativeCoverConstant k A := by
  unfold derivativeCoverConstant
  positivity

private theorem separation_le_of_small_values {U : Set ℝ} (hUc : U.OrdConnected)
    {F : ℕ → ℝ → ℝ} {k : ℕ} (hF : IsDerivChain k F U) (hk : 1 ≤ k)
    {A ε d : ℝ} (hA : 0 < A) (hε : 0 < ε) (hd : 0 < d)
    (hlow : ∀ x ∈ U, A ≤ |F k x|) (x : Fin (k + 1) → ℝ)
    (hxmono : StrictMono x) (hxmem : ∀ i, x i ∈ U)
    (hxval : ∀ i, |F 0 (x i)| < ε)
    (hxsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) :
    d ≤ (((k + 1).factorial : ℝ) * ε / A) ^ ((k : ℝ)⁻¹) := by
  classical
  obtain ⟨ξ, hξmem, hξ⟩ :=
    exists_chain_eq_factorial_mul_coeff hUc k hF x hxmono hxmem
  have hξU : ξ ∈ U := hUc.out (hxmem 0) (hxmem (Fin.last k)) hξmem
  let P : Polynomial ℝ := Lagrange.interpolate Finset.univ x fun i => F 0 (x i)
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin (k + 1))) := hxmono.injective.injOn
  have hdeg : P.degree < ((Finset.univ : Finset (Fin (k + 1))).card : ℕ) :=
    Lagrange.degree_interpolate_lt _ hinj
  have hcoeff : P.coeff k = ∑ i, F 0 (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
    have h := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (k + 1))))
      (v := x) (P := P) hinj hdeg
    have hc : (Finset.univ : Finset (Fin (k + 1))).card - 1 = k := by simp
    rw [hc] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by
      dsimp only [P]
      rw [Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)]
  have hprod (i : Fin (k + 1)) : d ^ k ≤ |∏ j ∈ Finset.univ.erase i, (x i - x j)| := by
    rw [Finset.abs_prod]
    have hcard : (Finset.univ.erase i).card = k := by simp
    calc d ^ k = ∏ _j ∈ Finset.univ.erase i, d := by rw [Finset.prod_const, hcard]
      _ ≤ ∏ j ∈ Finset.univ.erase i, |x i - x j| :=
        Finset.prod_le_prod (fun _ _ => hd.le)
          (fun j hj => hxsep i j (Finset.ne_of_mem_erase hj).symm)
  have hcbound : |P.coeff k| ≤ ((k : ℝ) + 1) * ε / d ^ k := by
    rw [hcoeff]
    calc |∑ i, F 0 (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)|
        ≤ ∑ i, |F 0 (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (k + 1), ε / d ^ k := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_div]
        exact (div_le_div_of_nonneg_right (hxval i).le (abs_nonneg _)).trans
          (div_le_div_of_nonneg_left hε.le (by positivity) (hprod i))
      _ = ((k : ℝ) + 1) * ε / d ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  have hfk : A ≤ (k.factorial : ℝ) * |P.coeff k| := by
    have h := hlow ξ hξU
    rw [hξ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (k.factorial : ℝ))] at h
    exact h
  have hkey : d ^ k ≤ ((k + 1).factorial : ℝ) * ε / A := by
    have hbound := hfk.trans (mul_le_mul_of_nonneg_left hcbound
      (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)))
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < d ^ k)] at hbound
    rw [le_div_iff₀ hA, Nat.factorial_succ]
    push_cast
    nlinarith only [hbound]
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ d ^ k) hkey
    (by positivity : 0 ≤ (k : ℝ)⁻¹)
  rwa [← Real.rpow_natCast d k, ← Real.rpow_mul hd.le,
    mul_inv_cancel₀ hkR.ne', Real.rpow_one] at hroot

private theorem finite_cover_of_packing_bound (S : Set ℝ) (k : ℕ) {d : ℝ} (hd : 0 < d)
    (hcard : ∀ T : Finset ℝ, (∀ x ∈ T, x ∈ S) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → d ≤ |x - y|) → T.card ≤ k) :
    ∃ T : Finset ℝ, T.card ≤ k ∧ ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ d := by
  classical
  let C : Set ℕ := {n | ∃ T : Finset ℝ, (∀ x ∈ T, x ∈ S) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → d ≤ |x - y|) ∧ T.card = n}
  have hne : C.Nonempty := ⟨0, ∅, by simp, by simp, by simp⟩
  have hbdd : BddAbove C := ⟨k, by
    rintro n ⟨T, hT, hsep, rfl⟩
    exact hcard T hT hsep⟩
  obtain ⟨T, hT, hsep, hTc⟩ := Nat.sSup_mem hne hbdd
  refine ⟨T, hcard T hT hsep, fun x hx => ?_⟩
  by_contra h
  push Not at h
  have hxT : x ∉ T := by
    intro hxT
    have := h x hxT
    simp only [sub_self, abs_zero] at this
    linarith only [hd, this]
  have hins : (insert x T).card ∈ C := by
    refine ⟨insert x T, ?_, ?_, rfl⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hT y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with hyx | hyT
      · subst y
        rcases Finset.mem_insert.mp hz with hzx | hzT
        · exact (hyz hzx.symm).elim
        · exact (h z hzT).le
      · rcases Finset.mem_insert.mp hz with hzx | hzT
        · subst z
          rw [abs_sub_comm]
          exact (h y hyT).le
        · exact hsep y hyT z hzT hyz
  have hle := le_csSup hbdd hins
  rw [Finset.card_insert_of_notMem hxT, hTc] at hle
  omega

/-- A lower bound on a derivative gives a cover by at most its order many balls, with radii
proportional to the corresponding root of the sublevel threshold. -/
theorem exists_sublevel_cover_of_derivative_lower {U : Set ℝ} (hUc : U.OrdConnected)
    {F : ℕ → ℝ → ℝ} {k : ℕ} (hF : IsDerivChain k F U) (hk : 1 ≤ k)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) (hlow : ∀ x ∈ U, A ≤ |F k x|) :
    ∃ T : Finset ℝ, T.card ≤ k ∧ ∀ x ∈ U, |F 0 x| < ε →
      ∃ y ∈ T, |x - y| ≤ derivativeCoverConstant k A * ε ^ ((k : ℝ)⁻¹) := by
  classical
  let L : ℝ := (((k + 1).factorial : ℝ) * ε / A) ^ ((k : ℝ)⁻¹)
  have hL : 0 < L := by dsimp [L]; positivity
  have hscale : derivativeCoverConstant k A * ε ^ ((k : ℝ)⁻¹) = 2 * L := by
    dsimp [derivativeCoverConstant, L]
    rw [show ((k + 1).factorial : ℝ) * ε / A =
      (((k + 1).factorial : ℝ) / A) * ε by ring,
      Real.mul_rpow (by positivity) hε.le]
    ring
  rw [hscale]
  have hpacking (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ U ∧ |F 0 x| < ε)
      (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * L ≤ |x - y|) : s.card ≤ k := by
    by_contra hc
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := s) (n := k + 1) (by omega)
    let x : Fin (k + 1) → ℝ := fun i => t.orderIsoOfFin htcard i
    have hxmem (i : Fin (k + 1)) : x i ∈ s := hts (t.orderIsoOfFin htcard i).2
    have hxmono : StrictMono x := fun _ _ hij => (t.orderIsoOfFin htcard).strictMono hij
    have hbound := separation_le_of_small_values hUc hF hk hA hε
      (by positivity : 0 < 2 * L) hlow x hxmono
      (fun i => (hs _ (hxmem i)).1) (fun i => (hs _ (hxmem i)).2)
      (fun i j hij => hsep _ (hxmem i) _ (hxmem j) (hxmono.injective.ne hij))
    change 2 * L ≤ L at hbound
    linarith only [hL, hbound]
  obtain ⟨T, hTc, hcover⟩ := finite_cover_of_packing_bound
    {x ∈ U | |F 0 x| < ε} k (by positivity : 0 < 2 * L) hpacking
  exact ⟨T, hTc, fun x hx hval => hcover x ⟨hx, hval⟩⟩

#print axioms exists_sublevel_cover_of_derivative_lower

end GaloisForLFunctions.InfiniteRankWeilTheory
