import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.VariationOfTheFactorialPrimeDiscrepancy

/-!
# Opposite odd-quotient discrepancies across a terminal block

Completing an interior interval forces an opposite flank. Crossing neighboring
numerators costs only the divisors of the integers crossed, uniformly in the
two intervals and in the choice of numerators retained from the block.
-/

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private theorem oriented_le_abs {s : ℝ} (hs : s=1 ∨ s= -1) (x : ℝ) : s*x ≤ |x| := by
  rcases hs with rfl|rfl
  · simpa only [one_mul] using le_abs_self x
  · simpa only [neg_one_mul] using (neg_le_abs x)

/-- A discrepancy beyond the complete square-root bound on one interval
forces the opposite sign on one of its two exact complementary intervals. -/
private theorem other_interval {H a b : ℕ} {C B s : ℝ} (hC : 0≤C) (hB : 4*C≤B)
    (hs : s=1 ∨ s= -1) (hab : a≤b) (ha : Real.sqrt H<a)
    (hall : ∀ L : ℕ, H≤L → |oddQuotientPrimeExcess (Finset.Ioc ⌊Real.sqrt H⌋₊ L) H| ≤ C*Real.sqrt H)
    (hbig : B*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H) :
    ∃ l u : ℕ, ((l=⌊Real.sqrt H⌋₊ ∧ u=a-1) ∨ (l=b ∧ u=H)) ∧
      (∀ n ∈ Finset.Ioc l u, Real.sqrt H<n) ∧
      (B/4)*Real.sqrt H < (-s)*oddQuotientPrimeExcess (Finset.Ioc l u) H := by
  let r := ⌊Real.sqrt H⌋₊
  let L := max b H
  let O := fun (S : Finset ℕ) => oddQuotientPrimeExcess S H
  have hra : r<a := (Nat.floor_lt (Real.sqrt_nonneg _)).mpr ha
  have hpos : 1≤a := Nat.zero_lt_of_lt hra
  have hm : Finset.Ioc (a-1) b=Finset.Icc a b := by
    ext n; simp only [Finset.mem_Ioc,Finset.mem_Icc]; omega
  have hend : Finset.Ioc b L=Finset.Ioc b H := by
    ext n; simp only [Finset.mem_Ioc,L]; omega
  have split : O (Finset.Ioc r L) =
      O (Finset.Ioc r (a-1))+O (Finset.Icc a b)+O (Finset.Ioc b H) := by
    dsimp only [O,oddQuotientPrimeExcess]
    rw [← Finset.sum_Ioc_consecutive _ (by omega : r≤b) (le_max_left b H),
        ← Finset.sum_Ioc_consecutive _ (by omega : r≤a-1) (by omega : a-1≤b),hm,hend]
  have hnet := (oriented_le_abs hs _).trans (hall L (le_max_right ..))
  change s*O (Finset.Ioc r L) ≤ _ at hnet
  rw [split] at hnet
  by_cases hl : (B/4)*Real.sqrt H < (-s)*O (Finset.Ioc r (a-1))
  · exact ⟨r,a-1,Or.inl ⟨rfl,rfl⟩,fun n hn => (Nat.floor_lt (Real.sqrt_nonneg _)).mp
      (Finset.mem_Ioc.mp hn).1,hl⟩
  · refine ⟨b,H,Or.inr ⟨rfl,rfl⟩,fun n hn => ha.trans_le (Nat.cast_le.mpr
      (hab.trans (Finset.mem_Ioc.mp hn).1.le)),?_⟩
    change _ < (-s)*O (Finset.Ioc b H)
    change B*Real.sqrt H < s*O (Finset.Icc a b) at hbig
    linarith only [hnet,hbig,le_of_not_gt hl,mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg H),
      mul_nonneg hC (Real.sqrt_nonneg H)]

private theorem eventual_log_price {d A : ℝ} (hd : 0<d) (hA : 0<A) :
    ∀ᶠ x : ℝ in atTop, 2*Real.log x+2+2*|Real.eulerMascheroniConstant| ≤ (A/16)*x^d := by
  have hlog := (isLittleO_log_rpow_atTop hd).bound (show 0<A/64 by positivity)
  have hex := (tendsto_rpow_atTop hd).const_mul_atTop (show 0<A/32 by positivity)
  filter_upwards [hlog,hex.eventually_ge_atTop (2+2*|Real.eulerMascheroniConstant|),
    eventually_ge_atTop (1:ℝ)] with x h hx hx1
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith only [hx1]) d)] at h
  change _ ≤ (A/32)*x^d at hx
  linarith only [h,hx]

private theorem block_cost {H M : ℕ} {d A E : ℝ} (hM : 1≤M) (hMH : M≤H) (hA : 0<A)
    (hd : (H:ℝ)^d*(H:ℝ)^d ≤ E) (hE : 40 ≤ (A/16)*E)
    (hlog : 2*Real.log H+2+2*|Real.eulerMascheroniConstant| ≤ (A/16)*(H:ℝ)^d)
    (hwidth : (H:ℝ)-M ≤ (H:ℝ)^(1/2+d)) :
    ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H ≤
      (A*E/8)*Real.sqrt H := by
  have hp : 0<(H:ℝ) := Nat.cast_pos.mpr (hM.trans hMH)
  have hR : 0≤(H:ℝ)^d := Real.rpow_nonneg hp.le _
  have hpos : 0≤2*Real.log H+2+2*|Real.eulerMascheroniConstant| := by
    have h := Real.log_natCast_nonneg H
    positivity
  rw [Real.rpow_add hp,← Real.sqrt_eq_rpow] at hwidth
  have h₁ := mul_le_mul hwidth hlog hpos (mul_nonneg (Real.sqrt_nonneg H) hR)
  have h₂ := mul_le_mul_of_nonneg_left hd (mul_nonneg (by positivity : 0≤A/16) (Real.sqrt_nonneg H))
  linarith only [h₁,h₂,mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg H)]

private theorem persist {s B : ℝ} (hs : s=1 ∨ s= -1) (S E : Finset ℕ) (hne : E.Nonempty)
    {M H : ℕ} (hM : 1≤M) (hMH : M≤H) (hE : E ⊆ Finset.Icc M H)
    (hmargin : B/4*Real.sqrt H < s*oddQuotientPrimeExcess S H)
    (hcost : ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H ≤ B/8*Real.sqrt H) :
    (B/8)*Real.sqrt H < s*commonOddQuotientPrimeExcess S E := by
  have hdiff := (oriented_le_abs hs _).trans ((commonOddQuotientPrimeExcess_change S E hM hMH hne hE).trans hcost)
  linarith only [hdiff,hmargin]

/-- Uniformly at late scales, every large signed interior interval has a
compensating flank. Both signs persist on every nonempty subset of each
terminal block of the indicated width. -/
theorem eventually_paired_quotient_intervals {A g : ℝ} (hA : 0<A) (hg : 0<g) :
    let d := min (g/12) (1/4)
    ∀ᶠ T : ℝ in atTop, ∀ (H a b : ℕ) (s : ℝ), Real.exp T≤H → (H:ℝ)^(g/6)≤Real.exp (g*T) →
      (s=1 ∨ s= -1) → a≤b → Real.sqrt H<a →
      A*Real.exp (g*T)*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H →
      ∃ l u : ℕ, ((l=⌊Real.sqrt H⌋₊ ∧ u=a-1) ∨ (l=b ∧ u=H)) ∧
        ∀ M : ℕ, 1≤M → M≤H → (H:ℝ)-M≤(H:ℝ)^(1/2+d) →
          ∀ J : Finset ℕ, J.Nonempty → J ⊆ Finset.Icc M H →
            A/8*Real.exp (g*T)*Real.sqrt H < s*commonOddQuotientPrimeExcess (Finset.Icc a b) J ∧
            A/8*Real.exp (g*T)*Real.sqrt H < (-s)*commonOddQuotientPrimeExcess (Finset.Ioc l u) J := by
  obtain ⟨C,hC,hall⟩ := oddQuotientPrimeExcess_complete_above_sqrt
  let d := min (g/12) (1/4)
  have hd : 0<d := lt_min (by positivity) (by norm_num)
  obtain ⟨U,hlog⟩ := eventually_atTop.mp (eventual_log_price hd hA)
  have hE := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hg)
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (max U 1),
    (hE.const_mul_atTop hA).eventually_ge_atTop (4*C),
    (hE.const_mul_atTop (show 0<A/16 by positivity)).eventually_ge_atTop 40] with T hU hbig h40
  intro H a b s hHX hpow hs hab hroot hmid
  let E := Real.exp (g*T)
  let B := A*E
  have hH : 1≤(H:ℝ) := (le_max_right U 1).trans (hU.trans hHX)
  obtain ⟨l,u,hside,_,hother⟩ := other_interval hC hbig hs hab hroot (hall H) hmid
  refine ⟨l,u,hside,fun M hM hMH hwidth J hJ hsub => ?_⟩
  have hd₂ : (H:ℝ)^d*(H:ℝ)^d ≤ E := by
    rw [← Real.rpow_add (by linarith only [hH] : 0<(H:ℝ))]
    exact (Real.rpow_le_rpow_of_exponent_le hH (by linarith only [min_le_left (g/12) (1/4:ℝ)] : d+d≤g/6)).trans hpow
  have hcost := block_cost hM hMH hA hd₂ h40 (hlog _ ((le_max_left U 1).trans (hU.trans hHX))) hwidth
  have hB : 0≤B := mul_nonneg hA.le (Real.exp_pos _).le
  have hlow := persist hs (Finset.Icc a b) J hJ hM hMH hsub
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith only [hB] : B/4≤B) (Real.sqrt_nonneg _)) hmid) hcost
  have hneg : -s=1 ∨ -s= -1 := hs.elim (fun h => Or.inr (by rw [h])) (fun h => Or.inl (by rw [h,neg_neg]))
  have hhigh := persist hneg (Finset.Ioc l u) J hJ hM hMH hsub hother hcost
  have heq : A/8*Real.exp (g*T)=B/8 := by dsimp only [B,E]; ring
  rw [heq]; exact ⟨hlow,hhigh⟩

#print axioms eventually_paired_quotient_intervals
end GaloisForLFunctions.ExclusionOfTheCriticalState
