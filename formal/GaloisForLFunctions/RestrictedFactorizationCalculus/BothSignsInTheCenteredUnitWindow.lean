import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeErrorInTheCenteredUnitWindow
import GaloisForLFunctions.RHTower.ChebyshevThetaLittlewoodOmega

/-!
# Both signs of the centered unit-cofactor reading at the critical exponent

A record of one oriented prime error divided by the square root controls
its own earlier endpoint. Littlewood excursions therefore pass to a
single centered quotient window, simultaneously for every choice of
the signs of proper prime powers.
-/
noncomputable section
open Finset Filter ArithmeticFunction
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev L (t : ℝ) := Real.log (Real.log (Real.log t))
private abbrev c := RHTower.littlewoodConst/28

private theorem prime_excursions (σ : ℝ) (dir : σ=1 ∨ σ= -1) :
    ∃ᶠ x : ℝ in atTop,c*Real.sqrt x*L x < σ*(Chebyshev.theta x-x) := by
  rcases dir with rfl | rfl
  · simpa only [one_mul] using RHTower.chebyshevTheta_sub_omega_pm_littlewood.2
  · exact RHTower.chebyshevTheta_sub_omega_pm_littlewood.1.mono (fun x large => by
      change _ < (-1:ℝ)*_
      linarith only [large])

/-- Arbitrarily late record highs of either oriented normalized prime error
retain the Littlewood lower bound. Each controls every earlier integer. -/
theorem oriented_prime_error_records (σ : ℝ) (dir : σ=1 ∨ σ= -1) (B : ℝ) (N : ℕ) :
    ∃ m : ℕ,N ≤ m ∧ B < σ*ordinaryThetaError m/Real.sqrt m ∧
      c/2*L m < σ*ordinaryThetaError m/Real.sqrt m ∧
      ∀ k : ℕ,k ≤ m → σ*ordinaryThetaError k/Real.sqrt k ≤ σ*ordinaryThetaError m/Real.sqrt m := by
  let H := fun k : ℕ => σ*ordinaryThetaError k/Real.sqrt k
  have cpos : 0<c := div_pos RHTower.littlewoodConst_pos (by norm_num)
  let M := max N 16
  let A := ∑ k ∈ Icc 0 M,|H k|
  let V := max (max A B) 2
  have big := RHTower.tendsto_logLogLog_atTop.eventually_ge_atTop ((V+1)/(c/2))
  obtain ⟨x,hx,large,logsize⟩ := frequently_atTop.mp ((prime_excursions σ dir).and_eventually big) 16
  let n := ⌊x⌋₊
  have room := (div_le_iff₀ (half_pos cpos)).mp logsize
  have two : (2:ℝ) ≤ V := le_max_right .. 
  have height : V<c/2*L x := by
    change V+1 ≤ L x*(c/2) at room
    linarith only [room]
  have L0 : 0<L x := pos_of_mul_pos_right (by linarith only [height,two] : 0<c/2*L x) (half_pos cpos).le
  have xp : 1 ≤ x := by linarith only [hx]
  have np : 1 ≤ n := Nat.le_floor xp
  have fl : (n:ℝ) ≤ x := Nat.floor_le (zero_le_one.trans xp)
  have θ : Chebyshev.theta (n:ℝ)=Chebyshev.theta x := by simp [Chebyshev.theta,n]
  have gap : σ*(x-(n:ℝ)) ≥ -1 := by
    rcases dir with h | h <;> rw [h] <;> linarith only [fl,Nat.lt_floor_add_one x]
  have floorLarge : c*Real.sqrt x*L x-1 < σ*ordinaryThetaError n := by
    change _<σ*(Chebyshev.theta n-n)
    rw [θ]
    linarith only [gap,large]
  have root := Real.sqrt_le_sqrt fl
  have ge := Real.one_le_sqrt.mpr xp
  have rn := Real.sqrt_pos.mpr (Nat.cast_pos.mpr np)
  have extra := mul_le_mul_of_nonneg_left ge (by linarith only [height,two] : 0 ≤ c/2*L x)
  have absorb := mul_le_mul_of_nonneg_left root (mul_nonneg (half_pos cpos).le L0.le)
  have leader : c/2*L x < H n := (lt_div_iff₀ rn).mpr (by linarith only [absorb,extra,floorLarge,height,two])
  obtain ⟨m,hm,record⟩ := Finset.exists_max_image (Icc 0 n) H ⟨n,mem_Icc.mpr ⟨Nat.zero_le n,le_rfl⟩⟩
  have best := record n (mem_Icc.mpr ⟨Nat.zero_le _,le_rfl⟩)
  have above : A<H m := (le_max_left A B).trans_lt ((le_max_left (max A B) 2).trans_lt (height.trans (leader.trans_le best)))
  have mlarge : M< m := by
    by_contra! small
    have cap := single_le_sum (s := Icc 0 M) (f := fun k => |H k|) (fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨Nat.zero_le m,small⟩)
    exact (not_le_of_gt above) ((le_abs_self _).trans cap)
  have mx := (Nat.cast_le.mpr (mem_Icc.mp hm).2).trans fl
  have m16 : (16:ℝ) ≤ m := by exact_mod_cast (le_max_right N 16).trans mlarge.le
  have ml : 1 < Real.log m := by
    apply (Real.lt_log_iff_exp_lt (by linarith : 0<(m:ℝ))).mpr
    exact Real.exp_one_lt_d9.trans_le (by linarith only [m16])
  have logs := Real.log_le_log (by linarith : 0<(m:ℝ)) mx
  have logs' := Real.log_le_log (zero_lt_one.trans ml) logs
  have Lorder := Real.log_le_log (Real.log_pos ml) logs'
  exact ⟨m,(le_max_left N 16).trans mlarge.le,
    (le_max_right A B).trans_lt ((le_max_left _ 2).trans_lt (height.trans (leader.trans_le best))),
    (mul_le_mul_of_nonneg_left Lorder (half_pos cpos).le).trans_lt (leader.trans_le best),
    fun k km => record k (mem_Icc.mpr ⟨Nat.zero_le _,km.trans (mem_Icc.mp hm).2⟩)⟩

/-- Both orientations have arbitrarily late Littlewood-size excursions
on the same observations for all admissible proper-power readings. -/
theorem simultaneous_littlewood_excursions_of_the_centered_unit_window :
    ∃ δ : ℝ,0<δ ∧ ∀ σ : ℝ,σ=1 ∨ σ= -1 →
      ∃ᶠ X : ℕ in atTop,∀ a : ArithmeticFunction ℝ,(∀ q,|a q| ≤ vonMangoldt q) →
        (∀ p,p.Prime → a p=roughOrdinaryPrimeWeight (logSquareCutoff X) p) →
        δ*Real.sqrt X*Real.log (Real.log (Real.log X)) < σ*centeredUnitWindow a (logSquareCutoff X) X := by
  have cpos : 0<c := div_pos RHTower.littlewoodConst_pos (by norm_num)
  obtain ⟨D,d0,paid⟩ := uniform_change_from_the_two_prime_errors
  obtain ⟨N,late⟩ := eventually_atTop.mp paid
  refine ⟨c/16,div_pos cpos (by norm_num),fun σ dir => frequently_atTop.mpr (fun T => ?_)⟩
  obtain ⟨m,ml,big,scale,record⟩ := oriented_prime_error_records σ dir (8*D+1) (max (max N T) 1)
  refine ⟨m,((le_max_right N T).trans (le_max_left _ 1)).trans ml,?_⟩
  obtain ⟨half,changeWeight⟩ := late m (((le_max_left N T).trans (le_max_left _ 1)).trans ml)
  let K := m/(logSquareCutoff m+1)
  let H := fun k : ℕ => σ*ordinaryThetaError k/Real.sqrt k
  have mp := (le_max_right (max N T) 1).trans ml
  have mr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr mp)
  have H0 : 0<H m := by change 0<σ*ordinaryThetaError m/Real.sqrt m; linarith only [big,d0]
  have atK := record K (Nat.div_le_self ..)
  have exactValue (k : ℕ) : H k*Real.sqrt k=σ*ordinaryThetaError k := by
    rcases Nat.eq_zero_or_pos k with rfl | kp
    · simp [H,ordinaryThetaError,Chebyshev.theta]
    exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr kp)).ne'
  have half' : (2:ℝ)*(K:ℝ) ≤ m := by exact_mod_cast half
  have root : Real.sqrt K ≤ (3/4)*Real.sqrt m := by
    have pos : 0 ≤ (3/4:ℝ)*Real.sqrt m := by positivity
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) pos).mp
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
    linarith only [half',Nat.cast_nonneg (α := ℝ) m]
  have lower : H m*Real.sqrt m/4 ≤ σ*(ordinaryThetaError m-ordinaryThetaError K) := by
    have hk := (mul_le_mul_of_nonneg_right atK (Real.sqrt_nonneg K)).trans (mul_le_mul_of_nonneg_left root H0.le)
    change H K*Real.sqrt K ≤ _ at hk
    rw [exactValue] at hk
    linarith only [hk,exactValue m]
  intro a dom same
  have cost := changeWeight a dom same
  have oriented : |σ*(centeredUnitWindow a (logSquareCutoff m) m-(ordinaryThetaError m-ordinaryThetaError K))| ≤ D*Real.sqrt m := by
    rcases dir with h | h <;> simpa only [h,one_mul,neg_one_mul,abs_neg] using cost
  have absorb := mul_lt_mul_of_pos_right big mr
  have reading := mul_lt_mul_of_pos_right scale mr
  change (8*D+1)*Real.sqrt m < H m*Real.sqrt m at absorb
  change c/2*L m*Real.sqrt m < H m*Real.sqrt m at reading
  linarith only [(abs_le.mp oriented).1,absorb,reading,lower,mr]

#print axioms simultaneous_littlewood_excursions_of_the_centered_unit_window
end GaloisForLFunctions.RestrictedFactorizationCalculus
