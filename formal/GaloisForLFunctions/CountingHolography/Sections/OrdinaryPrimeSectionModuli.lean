import GaloisForLFunctions.CountingHolography.Sections.SectionHeightsAndThePickIndex
import GaloisForLFunctions.CountingHolography.Sections.ProperPowerContactWindows

/-!
# Removing all proper powers from the prime-pair section test

At a fixed lower degree each spline atom samples a multiplicative window
of bounded width. Chebyshev's bound on proper powers controls the contact
mass in that window. Summing over the lower degree costs only the bounded
logarithmic mass of each atom. For effective divisors the resulting bound
is quadratic in total multiplicity, uniformly in all conductor degrees.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticFunction AbsoluteGeometryOfSpecZ
open BiScaleUncertainty.ChebyshevGauge

private def atomWidth : ℝ := Real.exp (Real.log 3 + 5 + 4)

private def meshAtom {N : ℕ} (i : Fin N) (n j : ℕ) : ℝ :=
  cubicSpline (Real.log ((j : ℝ) / n) - (Real.log 3 + 5) - Real.log ((i : ℝ) + 1))

private theorem sample_eq_atoms {N : ℕ} (a : Fin N → ℤ) (n j : ℕ) :
    degreeSample (packet a) n j = ∑ i, (a i : ℝ) * meshAtom i n j := rfl

private theorem atomWidth_ge_one : 1 ≤ atomWidth := by
  apply Real.one_le_exp
  linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]

private theorem atom_window {N n : ℕ} (hn : 0 < n) (i : Fin N) (j : ℕ)
    (hne : meshAtom i n j ≠ 0) :
    (n : ℝ) * ((i : ℝ) + 1) ≤ j ∧ (j : ℝ) ≤ atomWidth * (n * ((i : ℝ) + 1)) := by
  let q := (i : ℝ) + 1
  let s := Real.log 3 + 5
  have hq : 1 ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) i.val]
  have hs : 4 ≤ s := by dsimp [s]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hnorm : |Real.log ((j : ℝ) / n) - s - Real.log q| ≤ 4 :=
    le_of_not_gt fun h => hne (cubicSpline_eq_zero h)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hnorm
  have hj : j ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, zero_div, Real.log_zero] at hlo
    dsimp [s] at hlo
    linarith [Real.log_nonneg hq, Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < (j : ℝ) / n := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)) hn'
  have hq' : 0 < q := zero_lt_one.trans_le hq
  have hl := Real.exp_le_exp.mpr (show Real.log q ≤ Real.log ((j : ℝ) / n) by linarith only [hs,hlo])
  rw [Real.exp_log hq', Real.exp_log ht] at hl
  have hu := Real.exp_le_exp.mpr
    (show Real.log ((j : ℝ) / n) ≤ (s + 4) + Real.log q by linarith only [hhi])
  rw [Real.exp_log ht, Real.exp_add, Real.exp_log hq'] at hu
  change (n : ℝ) * q ≤ j ∧ (j : ℝ) ≤ Real.exp (s+4) * (n*q)
  exact ⟨by linarith only [(le_div_iff₀ hn').mp hl],
    by linarith only [(div_le_iff₀ hn').mp hu]⟩

private theorem meshAtom_le_one {N : ℕ} (i : Fin N) (n j : ℕ) : meshAtom i n j ≤ 1 :=
  (cubicSpline_le_half _).trans (by norm_num)

private theorem effective_harmonic_mass {N n : ℕ} (a : Fin N → ℤ) (ha : ∀ i, 0 ≤ a i)
    (hn : 0 < n) (S : Finset ℕ) :
    ∑ j ∈ S, degreeSample (packet a) n j/j ≤ atomWidth*∑ i, (a i : ℝ) := by
  simp_rw [sample_eq_atoms,sum_div,mul_div_assoc]
  rw [sum_comm,mul_sum]
  apply sum_le_sum
  intro i _
  rw [← mul_sum,mul_comm atomWidth]
  exact mul_le_mul_of_nonneg_left (harmonicSample_le S (by positivity : 0 < (n : ℝ)*((i : ℝ)+1))
    (zero_le_one.trans atomWidth_ge_one) (meshAtom_le_one i n) (atom_window hn i)) (by exact_mod_cast ha i)

private def properCost : ℝ := 3 * (Real.log 4 + 4) * atomWidth

/-- All effective spline divisors obey the same quadratic bound for the
proper-power rows, including when the horizon and mesh vary independently. -/
theorem properContactMass_le {N : ℕ} (a : Fin N → ℤ) (ha : ∀ i, 0 ≤ a i)
    (L n : ℕ) (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k ∧ ¬ k.Prime) :
    ∑ k ∈ S, contactMultiplicity (packet a) L n k * vonMangoldt k ≤
      (2 * atomWidth * properCost) * (∑ i, (a i : ℝ))^2 := by
  let J := Ioc n (n+L*n)
  let f := degreeSample (packet a) n
  let c := fun i => (a i : ℝ)
  let M := ∑ i, c i
  have hc (i : Fin N) : 0 ≤ c i := by
    dsimp only [c]
    exact_mod_cast ha i
  have hM : 0 ≤ M := sum_nonneg fun i _ => hc i
  have hD := atomWidth_ge_one
  have hC : 0 ≤ properCost := by unfold properCost atomWidth; positivity
  by_cases hn : n = 0
  · subst n
    simp only [contactMultiplicity, mul_zero, add_zero, Ioc_self, sum_empty, mul_zero, zero_mul,
      sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hD)) hC) (sq_nonneg _)
  have hn' := Nat.pos_of_ne_zero hn
  have hx (i : Fin N) : 0 < (n : ℝ) * ((i : ℝ)+1) := by positivity
  have ha1 (i : Fin N) (j : ℕ) : meshAtom i n j ≤ 1 := meshAtom_le_one i n j
  have hfr (j : ℕ) : f j = ∑ i, c i * meshAtom i n j := sample_eq_atoms a n j
  have hf0 (j : ℕ) : 0 ≤ f j := by
    rw [hfr]; exact sum_nonneg fun i _ => mul_nonneg (hc i) (cubicSpline_nonneg _)
  have hmass : ∑ j ∈ J, f j / j ≤ atomWidth*M := effective_harmonic_mass a ha hn' J
  have hrow (j : ℕ) (hj : j ∈ J) : ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * f (j*k) ≤ properCost*M := by
    have hj' : 0 < j := hn'.trans (mem_Ioc.mp hj).1
    simp_rw [hfr, mul_sum]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro i _
    calc ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * (c i * meshAtom i n (j*k))
        = c i * ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * meshAtom i n (j*k) := by
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by ring
      _ ≤ c i * properCost := mul_le_mul_of_nonneg_left
          (properPowerSample_le S _ hj' hS (hx i) hD (ha1 i) (atom_window hn' i)) (hc i)
      _ = _ := mul_comm _ _
  have h := properPowerPairing_le S J f f (mul_nonneg hC hM) hf0 hrow hmass
  refine h.trans (le_of_eq ?_)
  change 2 * (atomWidth*M) * (properCost*M) = (2*atomWidth*properCost)*M^2
  ring

/-- Integral section modulus using only residue conditions at ordinary prime degrees. -/
def ordinaryPrimeModulus {N : ℕ} (a : Fin N → ℤ) : ℕ :=
  ∏ k ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime, contactBase k ^
    ⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋₊

private theorem log_modulusOn (S : Finset ℕ) (e : ℕ → ℕ) :
    Real.log ((∏ k ∈ S, contactBase k ^ e k : ℕ) : ℝ) = ∑ k ∈ S, (e k : ℝ) * vonMangoldt k := by
  push_cast
  rw [Real.log_prod (fun k _ => (pow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℝ) < _) _).ne')]
  simp only [Real.log_pow, log_contactBase]

theorem log_ordinaryPrimeModulus {N : ℕ} (a : Fin N → ℤ) :
    Real.log (ordinaryPrimeModulus a) = ∑ k ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime,
      (⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋₊ : ℝ)*vonMangoldt k :=
  log_modulusOn _ _

/-- Removing repeated prime powers costs at most one uniform multiple of the
square of total multiplicity, for every effective divisor. -/
theorem effective_modulus_difference_bound :
    ∃ C : ℝ, ∀ (N : ℕ) (a : Fin N → ℤ), (∀ i, 0 ≤ a i) →
      0 ≤ Real.log (contactModulus a) - Real.log (ordinaryPrimeModulus a) ∧
      Real.log (contactModulus a) - Real.log (ordinaryPrimeModulus a) ≤ C * (∑ i, (a i : ℝ))^2 := by
  refine ⟨2*atomWidth*properCost, fun N a ha => ?_⟩
  let L := 3*windowEnd N
  let n := resolution a
  let S := (Icc 2 L).filter (fun k => ¬ k.Prime)
  let x := fun k => contactMultiplicity (packet a) L n k
  have hx (k : ℕ) : 0 ≤ x k := by
    have hf (j : ℕ) : 0 ≤ degreeSample (packet a) n j := by
      rw [sample_eq_atoms]
      exact sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast ha i) (cubicSpline_nonneg _)
    unfold x contactMultiplicity
    exact mul_nonneg (by positivity) (sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (hf _) (hf _)) (Nat.cast_nonneg _))
  have he : Real.log (contactModulus a) - Real.log (ordinaryPrimeModulus a) =
      ∑ k ∈ S, (⌊x k⌋₊ : ℝ) * vonMangoldt k := by
    unfold contactModulus ordinaryPrimeModulus
    rw [log_modulusOn, log_modulusOn]
    exact sub_eq_iff_eq_add.mpr ((sum_filter_add_sum_filter_not (Icc 2 L) Nat.Prime
      (fun k => (⌊x k⌋₊ : ℝ) * vonMangoldt k)).symm.trans (add_comm _ _))
  rw [he]
  refine ⟨sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg, ?_⟩
  refine (sum_le_sum (fun k (_ : k ∈ S) =>
    mul_le_mul_of_nonneg_right (Nat.floor_le (hx k)) vonMangoldt_nonneg)).trans ?_
  apply properContactMass_le a ha L n S
  intro k hk
  obtain ⟨hkI, hkp⟩ := mem_filter.mp hk
  exact ⟨lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp hkI).1, hkp⟩

/-- Keep the signed prime rows, allowing denominators at primes where
the ordinary contact is negative. -/
def ordinaryPrimeGenerator {N : ℕ} (a : Fin N → ℤ) : ℚ :=
  ∏ k ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime, (contactBase k : ℚ) ^
    ⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋

theorem log_ordinaryPrimeGenerator {N : ℕ} (a : Fin N → ℤ) :
    Real.log (ordinaryPrimeGenerator a : ℝ) = ∑ k ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime,
      (⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋ : ℝ)*vonMangoldt k := by
  unfold ordinaryPrimeGenerator
  push_cast
  rw [Real.log_prod fun k _ => (zpow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℝ)<_) _).ne']
  simp only [Real.log_zpow,log_contactBase]

theorem ordinaryPrimeGenerator_le_modulus {N : ℕ} (a : Fin N → ℤ) :
    ordinaryPrimeGenerator a ≤ (ordinaryPrimeModulus a : ℚ) := by
  have hg : 0 < ordinaryPrimeGenerator a := prod_pos fun k _ => zpow_pos (by exact_mod_cast contactBase_pos k) _
  have hm : 0 < ordinaryPrimeModulus a := prod_pos fun k _ => pow_pos (contactBase_pos k) _
  have he : Real.log (ordinaryPrimeGenerator a : ℝ) ≤ Real.log (ordinaryPrimeModulus a) := by
    rw [log_ordinaryPrimeGenerator,log_ordinaryPrimeModulus]
    refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
    let x := contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k
    have hf : ⌊x⌋ ≤ (⌊x⌋₊ : ℤ) := by rw [← Int.floor_toNat]; omega
    exact_mod_cast hf
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hg) (Nat.cast_pos.mpr hm)).mp he

private theorem abs_contact_le {N : ℕ} (a : Fin N → ℤ) (L n k : ℕ) :
    |contactMultiplicity (packet a) L n k| ≤ contactMultiplicity (packet (fun i => |a i|)) L n k := by
  have hf (j : ℕ) : |degreeSample (packet a) n j| ≤ degreeSample (packet (fun i => |a i|)) n j := by
    rw [sample_eq_atoms,sample_eq_atoms]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    have hmesh : 0 ≤ meshAtom i n j := cubicSpline_nonneg _
    rw [abs_mul,Int.cast_abs,abs_of_nonneg hmesh]
  unfold contactMultiplicity
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2/Real.sqrt k)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  exact div_le_div_of_nonneg_right (mul_le_mul (hf j) (hf (j*k)) (abs_nonneg _)
    ((abs_nonneg _).trans (hf j))) (Nat.cast_nonneg _)

/-- The size of a single contact is controlled by the coefficient mass
and the inverse square root of the lag, at every mesh and horizon. -/
theorem contactMultiplicity_size : ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ) (L r k : ℕ),
    |contactMultiplicity (packet a) L r k| ≤ C*(∑ i, |(a i : ℝ)|)^2/Real.sqrt k := by
  refine ⟨2*atomWidth,by linarith only [atomWidth_ge_one],fun N a L r k => ?_⟩
  let b := fun i => |a i|
  let f := degreeSample (packet b) r
  let M := ∑ i, |(a i : ℝ)|
  have hM : 0 ≤ M := sum_nonneg fun _ _ => abs_nonneg _
  have hb (i) : 0 ≤ (b i : ℝ) := by dsimp [b]; positivity
  have hf (j : ℕ) : 0 ≤ f j := by
    rw [show f j = _ from sample_eq_atoms b r j]
    exact sum_nonneg fun i _ => mul_nonneg (hb i) (cubicSpline_nonneg _)
  have htop (j : ℕ) : f j ≤ M := by
    rw [show f j = _ from sample_eq_atoms b r j]
    apply sum_le_sum
    intro i _
    exact (mul_le_of_le_one_right (hb i) (meshAtom_le_one i r j)).trans_eq Int.cast_abs
  refine (abs_contact_le a L r k).trans ?_
  by_cases hr : r = 0
  · subst r
    simp only [contactMultiplicity,mul_zero,add_zero,Ioc_self,sum_empty,mul_zero]
    exact div_nonneg (mul_nonneg (by linarith only [atomWidth_ge_one]) (sq_nonneg _)) (Real.sqrt_nonneg _)
  let J := Ioc r (r+L*r)
  have hm : ∑ j ∈ J, f j/j ≤ atomWidth*M := by
    simpa only [b,Int.cast_abs] using effective_harmonic_mass b (fun i => abs_nonneg _) (Nat.pos_of_ne_zero hr) J
  have hsum : ∑ j ∈ J, f j*f (j*k)/j ≤ (atomWidth*M)*M := calc
    _ ≤ ∑ j ∈ J, (f j/j)*M := sum_le_sum fun j _ => by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (htop _) (hf _)) (Nat.cast_nonneg _)
    _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hm hM
  change 2/Real.sqrt k * (∑ j ∈ J, f j*f (j*k)/j) ≤ 2*atomWidth*M^2/Real.sqrt k
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

private theorem active_atom {N r j : ℕ} (a : Fin N → ℤ) (h : degreeSample (packet a) r j ≠ 0) :
    ∃ i, a i ≠ 0 ∧ meshAtom i r j ≠ 0 := by
  by_contra! hn
  apply h
  rw [sample_eq_atoms]
  refine sum_eq_zero fun i _ => ?_
  by_cases hi : a i = 0
  · rw [hi,Int.cast_zero,zero_mul]
  · rw [hn i hi,mul_zero]

/-- A nonzero row requires two active conductor labels whose ratio is
within one fixed multiplicative factor of the lag. -/
theorem contactMultiplicity_support : ∃ D : ℝ, 1 ≤ D ∧ ∀ (N : ℕ) (a : Fin N → ℤ) (L r k : ℕ),
    contactMultiplicity (packet a) L r k ≠ 0 → ∃ i j, a i ≠ 0 ∧ a j ≠ 0 ∧
      (k:ℝ)*((i:ℝ)+1) ≤ D*((j:ℝ)+1) ∧ ((j:ℝ)+1) ≤ D*(k:ℝ)*((i:ℝ)+1) := by
  refine ⟨atomWidth,atomWidth_ge_one,fun N a L r k h => ?_⟩
  have hr : 0 < r := by
    by_contra! hr
    have he := Nat.eq_zero_of_le_zero hr
    simp [he,contactMultiplicity] at h
  obtain ⟨t,ht,htk⟩ : ∃ t, degreeSample (packet a) r t ≠ 0 ∧ degreeSample (packet a) r (t*k) ≠ 0 := by
    by_contra! hn
    apply h
    unfold contactMultiplicity
    rw [sum_eq_zero (fun t _ => ?_),mul_zero]
    by_cases ht : degreeSample (packet a) r t = 0
    · rw [ht,zero_mul,zero_div]
    · rw [hn t ht,mul_zero,zero_div]
  obtain ⟨i,hi,hi'⟩ := active_atom a ht
  obtain ⟨j,hj,hj'⟩ := active_atom a htk
  obtain ⟨h₁,h₂⟩ := atom_window hr i t hi'
  obtain ⟨h₃,h₄⟩ := atom_window hr j (t*k) hj'
  rw [Nat.cast_mul] at h₃ h₄
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  refine ⟨i,j,hi,hj,(mul_le_mul_iff_right₀ hr').mp ?_,(mul_le_mul_iff_right₀ hr').mp ?_⟩
  · linarith only [mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg (α := ℝ) k),h₄]
  · linarith only [mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (α := ℝ) k),h₃]

/-- Proper prime powers cost at most a universal quadratic amount on
arbitrary signed divisors. The additional fixed-horizon term is the
one-sided rounding error for negative valuations. -/
theorem signed_generator_difference_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
      |Real.log (generator a : ℝ) - Real.log (ordinaryPrimeGenerator a : ℝ)| ≤
        C * (∑ i, |(a i : ℝ)|)^2 + ∑ k ∈ Icc 2 (3*windowEnd N), vonMangoldt k := by
  refine ⟨2*atomWidth*properCost,by unfold properCost atomWidth; positivity,fun N a => ?_⟩
  let L := 3*windowEnd N
  let n := resolution a
  let S := (Icc 2 L).filter (fun k => ¬ k.Prime)
  let x := fun k => contactMultiplicity (packet a) L n k
  have hOrd : Real.log (ordinaryPrimeGenerator a : ℝ) =
      ∑ k ∈ (Icc 2 L).filter Nat.Prime, (⌊x k⌋ : ℝ)*vonMangoldt k := log_ordinaryPrimeGenerator a
  have he : Real.log (generator a : ℝ) - Real.log (ordinaryPrimeGenerator a : ℝ) =
      ∑ k ∈ S, (⌊x k⌋ : ℝ)*vonMangoldt k := by
    rw [hOrd,generator,log_contactGenerator]
    exact sub_eq_iff_eq_add.mpr ((sum_filter_add_sum_filter_not (Icc 2 L) Nat.Prime
      (fun k => (⌊x k⌋ : ℝ)*vonMangoldt k)).symm.trans (add_comm _ _))
  have hfloor (k : ℕ) : |(⌊x k⌋ : ℝ)| ≤ |x k|+1 := by
    rw [abs_le]
    constructor <;> linarith only [Int.floor_le (x k),Int.sub_one_lt_floor (x k),le_abs_self (x k),neg_le_abs (x k)]
  let y := fun k => contactMultiplicity (packet (fun i => |a i|)) L n k
  have hsum := properContactMass_le (fun i => |a i|) (fun i => abs_nonneg _) L n S (fun k hk =>
    ⟨lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp (mem_filter.mp hk).1).1,(mem_filter.mp hk).2⟩)
  simp only [Int.cast_abs] at hsum
  rw [he]
  calc |∑ k ∈ S, (⌊x k⌋ : ℝ)*vonMangoldt k| ≤ ∑ k ∈ S, |(⌊x k⌋ : ℝ)*vonMangoldt k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, (y k+1)*vonMangoldt k := by
      apply sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_right ((hfloor k).trans (add_le_add (abs_contact_le a L n k) le_rfl)) vonMangoldt_nonneg
    _ = (∑ k ∈ S, y k*vonMangoldt k) + ∑ k ∈ S, vonMangoldt k := by simp only [add_mul,one_mul,sum_add_distrib]
    _ ≤ _ := add_le_add hsum (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => vonMangoldt_nonneg))

private theorem effective_prime_pair (p m : ℕ) (i : Fin (p+1)) : 0 ≤ (m • primePair p) i := by
  simp only [primePair, Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, Pi.single_apply]
  split_ifs <;> positivity

/-- The uniform cofinal section test on effective prime pairs needs only
ordinary prime contact rows. The constant is independent of both primes
and multiplicities. -/
theorem riemannHypothesis_iff_ordinary_prime_modulus_bound :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ p : ℕ, p.Prime →
      ∃ᶠ m : ℕ in atTop, Real.log (ordinaryPrimeModulus (m • primePair p)) ≤
        radius (m • primePair p) + B * (m : ℝ)^2 := by
  obtain ⟨C, hC⟩ := effective_modulus_difference_bound
  have hm (p m : ℕ) : (∑ i, ((m • primePair p) i : ℝ)) = 2*(m : ℝ) := by
    simp [primePair, Pi.smul_apply, Pi.single_apply, mul_add, sum_add_distrib,
      Pi.add_apply, two_mul]
  rw [riemannHypothesis_iff_prime_modulus_bound]
  constructor
  · rintro ⟨B,h⟩
    refine ⟨B, fun p hp => (h p hp).mono fun m hx => ?_⟩
    linarith only [hx, (hC _ _ (effective_prime_pair p m)).1]
  · rintro ⟨B,h⟩
    refine ⟨B + 4*C, fun p hp => (h p hp).mono fun m hx => ?_⟩
    have he := (hC _ _ (effective_prime_pair p m)).2
    rw [hm] at he
    linarith only [he,hx]

/-- Cofinal fitting of the ordinary-prime modulus in the original real
radius is equivalent to RH, with no archimedean allowance. -/
theorem riemannHypothesis_iff_ordinary_prime_modulus_fits :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeModulus (m • primePair p)) ≤ radius (m • primePair p) := by
  constructor
  · intro h p hp
    obtain ⟨C,hC⟩ := effective_modulus_difference_bound
    exact ((riemannHypothesis_iff_prime_modulus_fits.mp h) p hp).mono fun m hm =>
      (sub_nonneg.mp (hC _ _ (effective_prime_pair p m)).1).trans hm
  · intro h
    exact riemannHypothesis_iff_ordinary_prime_modulus_bound.mpr ⟨0, fun p hp => by simpa using h p hp⟩

#print axioms contactMultiplicity_size
#print axioms contactMultiplicity_support
#print axioms signed_generator_difference_bound
#print axioms effective_modulus_difference_bound
#print axioms riemannHypothesis_iff_ordinary_prime_modulus_bound
#print axioms riemannHypothesis_iff_ordinary_prime_modulus_fits

end GaloisForLFunctions.CountingHolography.Sections
