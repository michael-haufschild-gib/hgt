import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The kernel filtration of directed prime contacts

The least allowed dilation d controls the first possible output of every
power of the directed divisor matrix. The earliest nonzero input appears
at d^k times its original address with coefficient w(d)^k. Thus the whole
kernel filtration agrees with the pure dilation, even on an interval
with a nonzero lower endpoint.
-/
noncomputable section
open Finset Matrix ArithmeticFunction
open scoped Classical
namespace GaloisForLFunctions.SignedArithmeticCorrespondences

private abbrev Site (N B : ℕ) := ↥(Ioc N B)

/-- The directed divisor contact with input at the smaller site. -/
def directedDivisorContact (w : ℕ → ℝ) (N B : ℕ) : Matrix (Site N B) (Site N B) ℝ :=
  fun i j => if j.val ∣ i.val then w (i.val/j.val) else 0

private theorem below {w : ℕ → ℝ} {d : ℕ} (low : ∀ n < d, w n=0) {N B : ℕ}
    {i j : Site N B} (lt : i.val < d*j.val) : directedDivisorContact w N B i j = 0 := by
  unfold directedDivisorContact
  split
  · apply low
    exact (Nat.div_lt_iff_lt_mul ((Nat.zero_le _).trans_lt (mem_Ioc.mp j.property).1)).mpr lt
  · rfl

private theorem boundary {w : ℕ → ℝ} {d N B : ℕ} {i j : Site N B}
    (eq : i.val = d*j.val) : directedDivisorContact w N B i j = w d := by
  have jp := (Nat.zero_le _).trans_lt (mem_Ioc.mp j.property).1
  simp only [directedDivisorContact,eq,dvd_mul_left,if_true,Nat.mul_div_cancel _ jp]

/-- Below the first reachable dilation the power matrix vanishes, and
on its boundary only the repeated least dilation can contribute. -/
theorem directed_dilation_power_boundary {w : ℕ → ℝ} {d : ℕ} (hd : 0 < d)
    (low : ∀ n < d, w n=0) (k N B : ℕ) (i j : Site N B) :
    (i.val < d^k*j.val → (directedDivisorContact w N B ^ k) i j=0) ∧
    (i.val = d^k*j.val → (directedDivisorContact w N B ^ k) i j = (w d)^k) := by
  let M := directedDivisorContact w N B
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero,one_mul]
    constructor
    · intro h
      have ne : i ≠ j := fun e => h.ne (congrArg Subtype.val e)
      simp [Matrix.one_apply,ne]
    · intro h
      have eq : i=j := Subtype.ext h
      simp [eq,Matrix.one_apply]
  | succ k ih =>
    have power : 0 < d^k := pow_pos hd _
    have mono {z : Site N B} (large : d*j.val ≤ z.val) :
        d^(k+1)*j.val ≤ d^k*z.val := by
      rw [pow_succ,mul_assoc]
      exact Nat.mul_le_mul_left _ large
    simp only [pow_succ,Matrix.mul_apply]
    constructor
    · intro h
      apply sum_eq_zero
      intro z _
      rcases lt_or_ge z.val (d*j.val) with small|large
      · rw [below low small,mul_zero]
      · rw [(ih i z).1 ((show i.val < d^(k+1)*j.val from h).trans_le (mono large)),zero_mul]
    · intro eq
      have jp := (mem_Ioc.mp j.property).1
      have dj : j.val ≤ d*j.val := by simpa using Nat.mul_le_mul_right j.val hd
      have top : d*j.val ≤ i.val := by
        rw [eq,mul_assoc]
        simpa using Nat.mul_le_mul_right (d*j.val) power
      let z : Site N B := ⟨d*j.val,mem_Ioc.mpr ⟨jp.trans_le dj,top.trans (mem_Ioc.mp i.property).2⟩⟩
      rw [sum_eq_single z]
      · have coord : i.val = d^k*z.val := by change _ = d^k*(d*j.val);rw [eq,mul_assoc]
        rw [(ih i z).2 coord,boundary (show z.val=d*j.val from rfl)]
      · intro u _ ne
        have hne : u.val ≠ d*j.val := fun e => ne (Subtype.ext e)
        rcases lt_or_gt_of_ne hne with small|large
        · rw [below low small,mul_zero]
        · have strict := Nat.mul_lt_mul_of_pos_left large power
          have hi : i.val < d^k*u.val := by rw [eq,mul_assoc];exact strict
          rw [(ih i u).1 hi,zero_mul]
      · intro absent
        exact (absent (mem_univ _)).elim

private theorem first_reading {w : ℕ → ℝ} {d : ℕ} (hd : 0 < d) (low : ∀ n < d,w n=0)
    {N B k : ℕ} (c : Site N B → ℝ) (i j : Site N B)
    (eq : i.val=d^k*j.val) (first : ∀ u : Site N B, u.val < j.val → c u=0) :
    ((directedDivisorContact w N B)^k *ᵥ c) i = (w d)^k*c j := by
  change (∑ u, ((directedDivisorContact w N B)^k) i u*c u)=_
  rw [sum_eq_single j]
  · rw [(directed_dilation_power_boundary hd low k N B i j).2 eq]
  · intro u _ ne
    rcases lt_or_gt_of_ne (fun e : u.val=j.val => ne (Subtype.ext e)) with small|large
    · rw [first u small,mul_zero]
    · have h := Nat.mul_lt_mul_of_pos_left large (pow_pos hd k)
      rw [(directed_dilation_power_boundary hd low k N B i u).1 (by simpa only [eq] using h),zero_mul]
  · intro absent
    exact (absent (mem_univ _)).elim

/-- The literal kernel of each power consists of inputs supported past
floor(B/d^k), independently of all weights at larger dilations. -/
theorem directed_dilation_power_kernel {w : ℕ → ℝ} {d : ℕ} (hd : 0 < d) (wd : w d ≠ 0)
    (low : ∀ n < d,w n=0) (N B k : ℕ) (c : Site N B → ℝ) :
    (directedDivisorContact w N B)^k *ᵥ c=0 ↔
      ∀ j : Site N B, j.val ≤ B/d^k → c j=0 := by
  constructor
  · intro killed
    by_contra! witness
    let S := (univ : Finset (Site N B)).filter (fun j => c j ≠ 0)
    obtain ⟨z,zB,zne⟩ := witness
    have existsSite : S.Nonempty := ⟨z,mem_filter.mpr ⟨mem_univ _,zne⟩⟩
    let j := S.min' existsSite
    have jS := min'_mem S existsSite
    have jB : j.val ≤ B/d^k := (min'_le S z (mem_filter.mpr ⟨mem_univ _,zne⟩)).trans zB
    have jpos := (mem_Ioc.mp j.property).1
    have pre : j.val ≤ d^k*j.val := by simpa using Nat.mul_le_mul_right j.val (pow_pos hd k)
    let i : Site N B := ⟨d^k*j.val,mem_Ioc.mpr ⟨jpos.trans_le pre,
      by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (pow_pos hd k)).mp jB⟩⟩
    have f := first_reading hd low c i j rfl (by
      intro u hu
      by_contra nonzero
      exact hu.not_ge (min'_le S u (mem_filter.mpr ⟨mem_univ _,nonzero⟩)))
    rw [killed,Pi.zero_apply] at f
    exact (mul_ne_zero (pow_ne_zero _ wd) (mem_filter.mp jS).2) f.symm
  · intro late
    funext i
    change (∑ u, ((directedDivisorContact w N B)^k) i u*c u)=0
    apply sum_eq_zero
    intro u _
    rcases le_or_gt u.val (B/d^k) with h|h
    · rw [late u h,mul_zero]
    · have hi := (Nat.div_lt_iff_lt_mul (pow_pos hd k)).mp h
      have pos : i.val < d^k*u.val := (mem_Ioc.mp i.property).2.trans_lt (by simpa only [Nat.mul_comm] using hi)
      rw [(directed_dilation_power_boundary hd low k N B i u).1 pos,zero_mul]

/-- The first nonzero power coefficient is attained whenever the interval
contains both endpoints of a repeated least dilation. -/
theorem directed_dilation_power_zero_iff {w : ℕ → ℝ} {d : ℕ} (hd : 0 < d) (wd : w d ≠ 0)
    (low : ∀ n < d,w n=0) (N B k : ℕ) :
    (directedDivisorContact w N B)^k=0 ↔ B < d^k*(N+1) := by
  constructor
  · intro zero
    by_contra! room
    have start : N+1 ≤ d^k*(N+1) := by simpa using Nat.mul_le_mul_right (N+1) (pow_pos hd k)
    let j : Site N B := ⟨N+1,mem_Ioc.mpr ⟨Nat.lt_succ_self _,start.trans room⟩⟩
    let i : Site N B := ⟨d^k*(N+1),mem_Ioc.mpr ⟨(Nat.lt_succ_self _).trans_le start,room⟩⟩
    have h := (directed_dilation_power_boundary hd low k N B i j).2 rfl
    rw [zero,Matrix.zero_apply] at h
    exact (pow_ne_zero _ wd) h.symm
  · intro short
    ext i j
    have lo := Nat.mul_le_mul_left (d^k) ((mem_Ioc.mp j.property).1 : N+1 ≤ j.val)
    exact (directed_dilation_power_boundary hd low k N B i j).1
      ((mem_Ioc.mp i.property).2.trans_lt (short.trans_le lo))

/-- On every integer window the directed Mangoldt kernel vanishes precisely
on vectors supported past floor(B/2^k) after k applications. -/
theorem directed_mangoldt_power_kernel (N B k : ℕ) (c : Site N B → ℝ) :
    (directedDivisorContact vonMangoldt N B)^k *ᵥ c=0 ↔
      ∀ j : Site N B, j.val ≤ B/2^k → c j=0 := by
  apply directed_dilation_power_kernel (by decide : 0 < 2)
  · rw [vonMangoldt_apply_prime Nat.prime_two];exact (Real.log_pos (by norm_num)).ne'
  · intro n hn
    rcases (show n=0 ∨ n=1 by omega) with rfl|rfl <;> simp

/-- The rank sequence of the finite directed contact matrix is determined
by its least nonzero dilation, with every floor and both endpoints exact. -/
theorem directed_dilation_power_rank {w : ℕ → ℝ} {d : ℕ} (hd : 0 < d) (wd : w d ≠ 0)
    (low : ∀ n < d,w n=0) (N B k : ℕ) :
    ((directedDivisorContact w N B)^k).rank = B/d^k-N := by
  let L := {j : Site N B // j.val ≤ B/d^k}
  let M := (directedDivisorContact w N B)^k
  let restrict : (Site N B → ℝ) →ₗ[ℝ] (L → ℝ) :=
    { toFun := fun f j => f j.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have surj : Function.Surjective restrict := by
    intro g
    refine ⟨fun j => if h : j.val ≤ B/d^k then g ⟨j,h⟩ else 0,?_⟩
    funext j
    change (if h : j.val.val ≤ B/d^k then g ⟨j.val,h⟩ else 0)=g j
    rw [dif_pos j.property]
  have same : LinearMap.ker M.mulVecLin = LinearMap.ker restrict := by
    ext c
    change M *ᵥ c=0 ↔ restrict c=0
    rw [directed_dilation_power_kernel hd wd low]
    exact ⟨fun h => funext fun j => h j.val j.property,
      fun h j hj => congrFun h (⟨j,hj⟩ : L)⟩
  let equivalence : L ≃ ↥(Ioc N (B/d^k)) :=
    { toFun := fun j => ⟨j.val.val,mem_Ioc.mpr ⟨(mem_Ioc.mp j.val.property).1,j.property⟩⟩
      invFun := fun j => ⟨⟨j.val,mem_Ioc.mpr ⟨(mem_Ioc.mp j.property).1,
          (mem_Ioc.mp j.property).2.trans (Nat.div_le_self ..)⟩⟩,(mem_Ioc.mp j.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card L = B/d^k-N := by
    rw [Fintype.card_congr equivalence,Fintype.card_coe,Nat.card_Ioc]
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hL := LinearMap.finrank_range_add_finrank_ker restrict
  rw [same] at hM
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,Module.finrank_pi,hcard] at hL
  change Module.finrank ℝ (LinearMap.range M.mulVecLin)=_
  omega

/-- All directed prime-contact power ranks coincide exactly with those of
the pure doubling shift. An arbitrary integer window can be used. -/
theorem directed_mangoldt_power_rank (N B k : ℕ) :
    ((directedDivisorContact vonMangoldt N B)^k).rank = B/2^k-N := by
  apply directed_dilation_power_rank (by decide : 0 < 2)
  · rw [vonMangoldt_apply_prime Nat.prime_two];exact (Real.log_pos (by norm_num)).ne'
  · intro n hn
    rcases (show n=0 ∨ n=1 by omega) with rfl|rfl <;> simp


end GaloisForLFunctions.SignedArithmeticCorrespondences
