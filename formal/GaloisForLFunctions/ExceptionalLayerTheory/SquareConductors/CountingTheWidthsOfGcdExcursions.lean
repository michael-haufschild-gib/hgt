import GaloisForLFunctions.ArithmeticPositiveDuality.TheWidthsOfDiscreteSuperlevelComponents
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingIntegerPowerComparisonsOnTheGcdGrid

/-!
# Counting component widths of the gcd shortfall

Integer power comparisons recover the integrated left and right widths
of shortfall excursions. Counting all rational levels with denominator J
has an explicit additive error of at most n² log(2)/J on n depths.
-/

noncomputable section
open Finset MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.ComponentWidths
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem gcd_level_rational (r : ℕ) {m k J : ℕ} (hm : 0 < m) (hk : 0<k) (hkJ : k≤J) :
    (octaveGcdProduct (m^r) (m^(r+1)))^J≤2^((J-k)*m^(r+1)) ↔
      Real.log 2*(k:ℝ)/J≤gcdRowDeficit r m := by
  let G := octaveGcdProduct (m^r) (m^(r+1))
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hJ : 0<(J:ℝ) := Nat.cast_pos.mpr (hk.trans_le hkJ)
  have hX : 0<(m:ℝ)^(r+1) := pow_pos (Nat.cast_pos.mpr hm) _
  have hτ := div_pos (mul_pos hl (Nat.cast_pos.mpr hk)) hJ
  rw [gcdRowDeficit,le_max_iff,or_iff_left hτ.not_ge]
  change G^J ≤ _ ↔ Real.log 2*(k:ℝ)/J≤Real.log 2-Real.log G/(m:ℝ)^(r+1)
  by_cases hG : G=0
  · rw [hG,zero_pow (hk.trans_le hkJ).ne',Nat.cast_zero,Real.log_zero,zero_div,sub_zero]
    exact iff_of_true (Nat.zero_le _) ((div_le_iff₀ hJ).mpr
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkJ) hl.le))
  have hpos : 0<(G:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hG)
  have hcast : G^J≤2^((J-k)*m^(r+1)) ↔ (G:ℝ)^J≤(2:ℝ)^((J-k)*m^(r+1)) := by norm_cast
  rw [hcast,←Real.log_le_log_iff (pow_pos hpos _) (by positivity),Real.log_pow,Real.log_pow,
    Nat.cast_mul,Nat.cast_sub hkJ,Nat.cast_pow]
  have hJ0 : (J:ℝ) ≠ 0 := hJ.ne'
  rw [le_sub_comm, div_le_iff₀ hX,
    show (Real.log 2-Real.log 2*(k:ℝ)/J)*(m:ℝ)^(r+1) = ((J:ℝ)-k)*(m:ℝ)^(r+1)*Real.log 2/J by
      field_simp <;> ring,
    le_div_iff₀ hJ, mul_comm (Real.log (G:ℝ))]

/-- Every row from the center to each of two prescribed depths passes
the same integer comparison. All operations in this test are natural ones. -/
def gcdRunPasses (r m i j J k : ℕ) : Prop :=
  (∀ a ∈ range (i+1), (octaveGcdProduct ((m-a)^r) ((m-a)^(r+1)))^J≤2^((J-k)*(m-a)^(r+1))) ∧
  ∀ a ∈ range (j+1), (octaveGcdProduct ((m+a)^r) ((m+a)^(r+1)))^J≤2^((J-k)*(m+a)^(r+1))

/-- Integer count of ordered pairs of depths and successful common levels. -/
def gcdRunLevelCount (r m n J : ℕ) : ℕ := by
  classical
  exact ∑ i ∈ range n, ∑ j ∈ range n, ((Icc 1 J).filter (gcdRunPasses r m i j J)).card

/-- Integrated product of the two widths of an actual gcd shortfall excursion. -/
def gcdPairedWidth (r m n : ℕ) : ℝ :=
  pairedWidth (fun i => gcdRowDeficit r (m-i)) (fun j => gcdRowDeficit r (m+j)) n

private theorem positive_gcd_height (r m : ℕ) :
    0≤gcdRowDeficit r m ∧ gcdRowDeficit r m≤Real.log 2 := by
  unfold gcdRowDeficit
  exact ⟨le_max_right _ _,max_le (sub_le_self _ (div_nonneg (Real.log_natCast_nonneg _) (by positivity)))
    (Real.log_nonneg (by norm_num))⟩

private theorem run_passes_iff {r m n i j k J : ℕ} (hn : n ≤ m) (hi : i<n) (hj : j<n)
    (hk : 0<k) (hkJ : k≤J) :
    gcdRunPasses r m i j J k ↔ Real.log 2*(k:ℝ)/J≤
      commonHeight (fun a => gcdRowDeficit r (m-a)) (fun a => gcdRowDeficit r (m+a)) i j := by
  rw [gcdRunPasses,commonHeight,le_min_iff,le_depthHeight_iff,le_depthHeight_iff]
  simp only [mem_range,Nat.lt_succ_iff]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun a ha => (gcd_level_rational r (by omega) hk hkJ).mp (h₁ a ha),
      fun a ha => (gcd_level_rational r (by omega) hk hkJ).mp (h₂ a ha)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun a ha => (gcd_level_rational r (by omega) hk hkJ).mpr (h₁ a ha),
      fun a ha => (gcd_level_rational r (by omega) hk hkJ).mpr (h₂ a ha)⟩

/-- The all-integer run count captures the joint widths up to one height
mesh for every pair of depths, independently of the power grid and center. -/
theorem gcd_width_integer_enclosure (r m n J : ℕ) (hn : n ≤ m) (hJ : 0<J) :
    let E := Real.log 2/J
    E*(gcdRunLevelCount r m n J:ℝ) ≤ gcdPairedWidth r m n ∧
      gcdPairedWidth r m n ≤ E*(gcdRunLevelCount r m n J:ℝ)+E*(n:ℝ)^2 := by
  classical
  let f := fun i => gcdRowDeficit r (m-i)
  let g := fun j => gcdRowDeficit r (m+j)
  let C := commonHeight f g
  let A := fun i j => ((Icc 1 J).filter (gcdRunPasses r m i j J)).card
  let E := Real.log 2/(J:ℝ)
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0<(J:ℝ) := Nat.cast_pos.mpr hJ
  have hE : 0<E := div_pos hl hp
  have bounds (i j : ℕ) (hi : i<n) (hj : j<n) :
      E*(A i j:ℝ)≤C i j ∧ C i j ≤ E*(A i j:ℝ)+E := by
    have hC : 0≤C i j := le_min
      ((le_depthHeight_iff f _ _).mpr fun a _ => (positive_gcd_height r (m-a)).1)
      ((le_depthHeight_iff g _ _).mpr fun a _ => (positive_gcd_height r (m+a)).1)
    have hu : C i j≤Real.log 2 := ((min_le_left (depthHeight f i) (depthHeight g j)).trans
      (((le_depthHeight_iff f _ i).mp le_rfl) i le_rfl)).trans (positive_gcd_height r _).2
    let z := C i j/E
    have hz : 0≤z := div_nonneg hC hE.le
    have htop : z≤(J:ℝ) := (div_le_iff₀ hE).mpr
      (hu.trans_eq (by dsimp only [E]; field_simp [hp.ne']))
    have hs : (Icc 1 J).filter (gcdRunPasses r m i j J)=Icc 1 ⌊z⌋₊ := by
      ext k
      simp only [mem_filter,mem_Icc]
      have he (hk : 0<k) (hkJ : k≤J) : gcdRunPasses r m i j J k ↔ (k:ℝ)≤z := by
        rw [run_passes_iff hn hi hj hk hkJ,le_div_iff₀ hE]
        change Real.log 2*(k:ℝ)/J≤C i j ↔ (k:ℝ)*E≤C i j
        rw [show (k:ℝ)*E=Real.log 2*k/J by dsimp only [E]; ring]
      constructor
      · rintro ⟨⟨hk,hkJ⟩,hpass⟩
        exact ⟨hk,(Nat.le_floor_iff hz).mpr ((he hk hkJ).mp hpass)⟩
      · rintro ⟨hk,hkz⟩
        have hk' := (Nat.le_floor_iff hz).mp hkz
        have hkJ := Nat.cast_le.mp (hk'.trans htop)
        exact ⟨⟨hk,hkJ⟩,(he hk hkJ).mpr hk'⟩
    have ha : A i j=⌊z⌋₊ := by simp [A,hs,Nat.card_Icc]
    have hlow := (le_div_iff₀ hE).mp (Nat.floor_le hz)
    have hhigh := (div_lt_iff₀ hE).mp (Nat.lt_floor_add_one z)
    rw [ha]
    constructor <;> linarith only [hlow,hhigh]
  have sum_bounds :
      (∑ i ∈ range n, ∑ j ∈ range n, E*(A i j:ℝ)) ≤ pairedWidth f g n ∧
      pairedWidth f g n ≤ ∑ i ∈ range n, ∑ j ∈ range n, (E*(A i j:ℝ)+E) := by
    constructor
    · exact sum_le_sum fun i hi => sum_le_sum fun j hj => (bounds i j (mem_range.mp hi) (mem_range.mp hj)).1
    · exact sum_le_sum fun i hi => sum_le_sum fun j hj => (bounds i j (mem_range.mp hi) (mem_range.mp hj)).2
  have hsum : (∑ i ∈ range n, ∑ j ∈ range n, E*(A i j:ℝ))=E*(gcdRunLevelCount r m n J:ℝ) := by
    simp only [gcdRunLevelCount,A,Nat.cast_sum,mul_sum]
  rw [hsum] at sum_bounds
  refine ⟨sum_bounds.1,sum_bounds.2.trans_eq ?_⟩
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,hsum]
  change E*_+(n:ℝ)*(n*E)=E*_+E*(n:ℝ)^2
  ring

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
