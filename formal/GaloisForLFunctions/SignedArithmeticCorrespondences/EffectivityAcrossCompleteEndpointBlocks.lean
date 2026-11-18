import GaloisForLFunctions.SignedArithmeticCorrespondences.GluingIntegerGraphsAtTheirQuotientEndpoints

/-!
# Effectivity across complete residue blocks

The height through M minus d copies of the height through ⌊M/d⌋ has large jumps
between consecutive residues. Glue all d residues and take two differences in
the block index. The polar slope disappears. Reflection of the two endpoint
indices pairs the remaining local factors and gives their sign.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset ArithmeticCastelnuovoSeveri _root_.RHTower

/-- The signed graph order of all lower graphs against one upper endpoint. -/
def prefixHeight (M : ℕ) : ℝ :=
  signedDivisorHeight 1 M M (fun _ => 1)
    (upperDivisor M (fun j => if j = M then 1 else 0))

private theorem prefix_arithmetic (M : ℕ) :
    prefixHeight M = ∑ j ∈ Icc 1 M, Real.log j := by
  rw [prefixHeight, height_eq_quotient, ← floorSummatory_chebyshevPsi]
  unfold floorSummatory
  cases M with
  | zero => simp
  | succ n =>
    refine sum_congr rfl fun i _ => ?_
    simp [apply_ite, ite_mul]

private theorem prefix_succ (M : ℕ) :
    prefixHeight (M+1) = prefixHeight M + Real.log (M+1) := by
  rw [prefix_arithmetic, prefix_arithmetic, sum_Icc_succ_top (Nat.succ_pos M), Nat.cast_succ]

private theorem prefix_shift (a d : ℕ) :
    prefixHeight (a+d) - prefixHeight a = ∑ j ∈ range d, Real.log (a+j+1 : ℕ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, prefix_succ, sum_range_succ, ← ih, Nat.cast_succ]
    ring

/-- All upper endpoints in one complete residue block against the dilation
difference of two full families of lower graphs. -/
def blockHeight (d n : ℕ) : ℝ :=
  ∑ r ∈ range d, (prefixHeight (d*n+r) - (d : ℝ)*prefixHeight n)

/-- The displacement of a pair of residues from the center of its block. -/
def offset (d r j : ℕ) : ℝ := ((r : ℝ) + j + 1) / d - 1

/-- Every pair of residues lies strictly between the adjacent integer offsets. -/
theorem offset_bounds {d r j : ℕ} (hr : r < d) (hj : j < d) :
    -1 < offset d r j ∧ offset d r j < 1 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hr)
  have hr' : (r : ℝ)+1 ≤ d := by exact_mod_cast hr
  have hj' : (j : ℝ)+1 ≤ d := by exact_mod_cast hj
  unfold offset
  constructor
  · have h : 0 < ((r:ℝ)+j+1)/d := by positivity
    linarith
  · have h : ((r:ℝ)+j+1)/d < 2 := (div_lt_iff₀ hd).mpr (by linarith)
    linarith

private theorem offset_reflect {d r j : ℕ} (hr : r < d) (hj : j < d) :
    offset d (d-1-r) (d-1-j) = -offset d r j := by
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hr)).ne'
  have e (k : ℕ) (hk : k < d) : ((d-1-k : ℕ) : ℝ) = d-1-k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  unfold offset
  rw [e r hr, e j hj]
  field_simp
  ring

/-- The centered change across two aligned residue blocks is a sum of log
factors with equal positive and negative offsets. -/
private theorem residue_increment (d : ℕ+) (n r : ℕ) (hr : r ∈ range (d : ℕ)) :
    (prefixHeight ((d : ℕ)*(n+1)+r) - (d : ℝ)*prefixHeight (n+1)) -
      (prefixHeight ((d : ℕ)*n+r) - (d : ℝ)*prefixHeight n) =
      ∑ j ∈ range (d : ℕ),
        (Real.log (d : ℕ) + Real.log (1 + offset d r j / (n+1))) := by
  have hd : 0 < ((d : ℕ) : ℝ) := Nat.cast_pos.mpr d.pos
  have hn : (0 : ℝ) < n+1 := by positivity
  have he : (d : ℕ)*(n+1)+r = ((d : ℕ)*n+r)+d := by ring
  rw [he, prefix_succ]
  have hstep := prefix_shift ((d : ℕ)*n+r) d
  calc _ = (prefixHeight (((d : ℕ)*n+r)+d)-prefixHeight ((d : ℕ)*n+r)) -
        (d : ℝ)*Real.log (n+1) := by ring
       _ = ∑ j ∈ range (d : ℕ), (Real.log (((d : ℕ)*n+r+j+1 : ℕ) : ℝ) - Real.log (n+1)) := by
         rw [hstep, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
       _ = _ := by
         refine sum_congr rfl fun j hj => ?_
         have hz := (offset_bounds (mem_range.mp hr) (mem_range.mp hj)).1
         have hpos : 0 < 1 + offset d r j/(n+1) := by
           have : -(n+1 : ℝ) < offset d r j := by linarith [Nat.cast_nonneg (R := ℝ) n]
           linarith only [(lt_div_iff₀ hn).mpr (show -1 * (n+1 : ℝ) < offset d r j by linarith)]
         rw [← Real.log_div (by positivity) hn.ne', ← Real.log_mul hd.ne' hpos.ne']
         congr 1
         push_cast
         unfold offset
         field_simp
         ring

private theorem block_increment (d : ℕ+) (n : ℕ) :
    blockHeight d (n+1) - blockHeight d n =
      ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ),
        (Real.log (d : ℕ) + Real.log (1 + offset d r j / (n+1))) := by
  rw [blockHeight,blockHeight,← sum_sub_distrib]
  exact sum_congr rfl fun r hr => residue_increment d n r hr

private theorem sum_reflect_offset (d : ℕ+) (F : ℝ → ℝ) :
    ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ), F (-offset d r j) =
      ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ), F (offset d r j) := by
  calc _ = ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ),
              F (offset d ((d : ℕ)-1-r) ((d : ℕ)-1-j)) := by
             refine sum_congr rfl fun r hr => sum_congr rfl fun j hj => ?_
             rw [offset_reflect (mem_range.mp hr) (mem_range.mp hj)]
       _ = _ := by
         simp_rw [sum_range_reflect (fun j => F (offset d _ j))]
         exact sum_range_reflect (fun r => ∑ j ∈ range (d : ℕ), F (offset d r j)) _

private theorem log_reflection {x z : ℝ} (hx : 1 ≤ x) (hz : -1 < z ∧ z < 1) :
    Real.log (1+z/x) + Real.log (1+(-z)/x) = Real.log (1-(z/x)^2) := by
  have hx' : 0 < x := by linarith
  have lo : -1 < z/x := (lt_div_iff₀ hx').mpr (by linarith [hz.1])
  have hi : z/x < 1 := (div_lt_iff₀ hx').mpr (by linarith [hz.2])
  rw [neg_div, ← Real.log_mul (by linarith) (by linarith)]
  congr 1
  ring

private theorem twice_increment (d : ℕ+) (n : ℕ) :
    2*(blockHeight d (n+1)-blockHeight d n) =
      ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ),
        (2*Real.log (d : ℕ) + Real.log (1-(offset d r j/(n+1))^2)) := by
  rw [block_increment, two_mul]
  conv_lhs =>
    rhs
    rw [← sum_reflect_offset d (fun z => Real.log (d : ℕ) + Real.log (1+z/(n+1)))]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun r hr => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  linarith only [log_reflection (x := (n:ℝ)+1) (by linarith [Nat.cast_nonneg (R := ℝ) n])
    (offset_bounds (mem_range.mp hr) (mem_range.mp hj))]

/-- Exact second difference of a complete signed block. Every summand is the
increase of a log factor supported on an opposing pair of residue offsets. -/
theorem block_curvature (d : ℕ+) (n : ℕ) :
    2*(blockHeight d (n+2)-2*blockHeight d (n+1)+blockHeight d n) =
      ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ),
        (Real.log (1-(offset d r j/((n:ℝ)+2))^2) -
         Real.log (1-(offset d r j/((n:ℝ)+1))^2)) := by
  have h := twice_increment d (n+1)
  push_cast at h
  simp only [show ∀ x : ℝ, x+1+1=x+2 by intro x; ring] at h
  calc _ = 2*(blockHeight d (n+2)-blockHeight d (n+1)) -
            2*(blockHeight d (n+1)-blockHeight d n) := by ring
       _ = _ := by
         rw [h, twice_increment, ← sum_sub_distrib]
         refine sum_congr rfl fun r _ => ?_
         rw [← sum_sub_distrib]
         refine sum_congr rfl fun j _ => ?_
         ring

private theorem log_factor_step {t z : ℝ} (ht : 2 ≤ t) (hz : -1 < z ∧ z < 1) :
    0 ≤ Real.log (1-(z/(t+1))^2) - Real.log (1-(z/t)^2) ∧
    Real.log (1-(z/(t+1))^2) - Real.log (1-(z/t)^2) ≤ 4/t^3 := by
  let A := 1-(z/t)^2
  let B := 1-(z/(t+1))^2
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by positivity
  have hzz : z^2 ≤ 1 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hz.2.le) (show 0 ≤ 1+z by linarith [hz.1])]
  have ht2 : 4 ≤ t^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ t+2 by linarith)]
  have hA : 1/2 ≤ A := by
    dsimp only [A]
    rw [div_pow]
    have h := (div_le_iff₀ (sq_pos_of_pos ht0)).mpr (show z^2 ≤ (1/2)*t^2 by linarith)
    linarith only [h]
  have hA0 : 0 < A := by linarith
  have he : B-A = z^2 * ((2*t+1)/(t^2*(t+1)^2)) := by
    dsimp only [A,B]
    field_simp
    ring
  have hBA : A ≤ B := by
    apply sub_nonneg.mp
    rw [he]
    positivity
  have hfrac : (2*t+1)/(t^2*(t+1)^2) ≤ 2/t^3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg (sq_nonneg t) (show 0 ≤ 3*t+2 by linarith)]
  have hdiff : B-A ≤ 2/t^3 := by
    rw [he]
    exact (mul_le_of_le_one_left (by positivity) hzz).trans hfrac
  change 0 ≤ Real.log B - Real.log A ∧ Real.log B - Real.log A ≤ 4/t^3
  refine ⟨sub_nonneg.mpr (Real.log_le_log hA0 hBA), ?_⟩
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hA0.trans_le hBA) hA0)
  rw [Real.log_div (hA0.trans_le hBA).ne' hA0.ne'] at hlog
  apply hlog.trans
  rw [show B/A-1 = (B-A)/A by field_simp]
  apply (div_le_iff₀ hA0).mpr
  calc B-A ≤ 2/t^3 := hdiff
       _ = 4/t^3 * (1/2) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

/-- An effective primitive mixed intersection on arbitrarily large ordinary-prime
supports. Its curvature is nonnegative and costs at most 2d²/(n+1)³, uniformly
in both the conductor and the modulus. -/
theorem block_curvature_bounds (d : ℕ+) (n : ℕ) (hn : 1 ≤ n) :
    let K := blockHeight d (n+2)-2*blockHeight d (n+1)+blockHeight d n
    0 ≤ K ∧ K ≤ 2 * ((d : ℕ) : ℝ)^2 / ((n : ℝ)+1)^3 := by
  intro K
  let t := (n : ℝ)+1
  have ht : 2 ≤ t := by dsimp only [t]; exact_mod_cast (show 2 ≤ n+1 by omega)
  let L (r j : ℕ) := Real.log (1-(offset d r j/(t+1))^2) - Real.log (1-(offset d r j/t)^2)
  have hK : 2*K = ∑ r ∈ range (d : ℕ), ∑ j ∈ range (d : ℕ), L r j := by
    simpa only [K,L,t,show ∀ x : ℝ, x+1+1=x+2 by intro x; ring] using block_curvature d n
  have hL {r j : ℕ} (hr : r ∈ range (d : ℕ)) (hj : j ∈ range (d : ℕ)) :
      0 ≤ L r j ∧ L r j ≤ 4/t^3 := log_factor_step ht (offset_bounds (mem_range.mp hr) (mem_range.mp hj))
  have hlo : 0 ≤ 2*K := hK.trans_ge (sum_nonneg fun r hr => sum_nonneg fun j hj => (hL hr hj).1)
  have hhi : 2*K ≤ ∑ _r ∈ range (d : ℕ), ∑ _j ∈ range (d : ℕ), 4/t^3 := by
    rw [hK]
    exact sum_le_sum fun r hr => sum_le_sum fun j hj => (hL hr hj).2
  simp only [sum_const, card_range, nsmul_eq_mul] at hhi
  change 0 ≤ K ∧ K ≤ 2 * ((d : ℕ) : ℝ)^2 / t^3
  constructor
  · linarith only [hlo]
  · linarith only [hhi]

/-- Height of one residue endpoint against the full lower family and its d-fold subtraction. -/
def residueHeight (d r n : ℕ) : ℝ := prefixHeight (d*n+r) - (d : ℝ)*prefixHeight n

/-- A local curvature after removing its first moment. The two elementary
logarithmic inequalities leave explicit, strictly positive denominators. -/
private theorem centered_log_bounds {t z : ℝ} (ht : 1 ≤ t) (hz : -1 < z ∧ z < 1) :
    let G := t*(t+1)*(Real.log (1+z/(t+1))-Real.log (1+z/t))+z
    z^2/(t+1+z) ≤ G ∧ G ≤ z^2/(t+z) := by
  dsimp only
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by positivity
  have htz : 0 < t+z := by linarith [hz.1]
  have htz' : 0 < t+1+z := by linarith
  let x := ((t+1+z)/(t+1))/((t+z)/t)
  have hx : 0 < x := div_pos (div_pos htz' ht1) (div_pos htz ht0)
  have he : Real.log (1+z/(t+1))-Real.log (1+z/t) = Real.log x := by
    rw [show 1+z/(t+1) = (t+1+z)/(t+1) by field_simp,
      show 1+z/t = (t+z)/t by field_simp, ← Real.log_div (div_pos htz' ht1).ne' (div_pos htz ht0).ne']
  rw [he]
  have hm : 0 ≤ t*(t+1) := (mul_pos ht0 ht1).le
  constructor
  · calc z^2/(t+1+z) = t*(t+1)*(1-x⁻¹)+z := by
           dsimp [x]
           field_simp
           ring
         _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hm) _
  · calc _ ≤ t*(t+1)*(x-1)+z :=
           add_le_add_right (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hm) _
         _ = z^2/(t+z) := by
           dsimp [x]
           field_simp
           ring

/-- For each individual residue the first moment is the entire term of order
1/n². After it is paid, every residual local contact has the sign of a square.
Summing this bound permits incomplete, asymmetric sets of residues. -/
theorem residue_curvature_bounds (d : ℕ+) (n r : ℕ) (hr : r < d) :
    let t := (n : ℝ)+1
    let K := residueHeight d r (n+2)-2*residueHeight d r (n+1)+residueHeight d r n
    let M := ∑ j ∈ range (d : ℕ), offset d r j
    (∑ j ∈ range (d : ℕ), (offset d r j)^2/(t+1+offset d r j)) ≤ t*(t+1)*K+M ∧
      t*(t+1)*K+M ≤ ∑ j ∈ range (d : ℕ), (offset d r j)^2/(t+offset d r j) := by
  intro t K M
  let F (z : ℝ) := t*(t+1)*(Real.log (1+z/(t+1))-Real.log (1+z/t))+z
  have hinc (m : ℕ) : residueHeight d r (m+1)-residueHeight d r m =
      ∑ j ∈ range (d : ℕ), (Real.log (d : ℕ)+Real.log (1+offset d r j/((m:ℝ)+1))) :=
    residue_increment d m r (mem_range.mpr hr)
  have hK : K = ∑ j ∈ range (d : ℕ),
      (Real.log (1+offset d r j/(t+1))-Real.log (1+offset d r j/t)) := by
    calc K = (residueHeight d r (n+2)-residueHeight d r (n+1)) -
             (residueHeight d r (n+1)-residueHeight d r n) := by dsimp [K]; ring
         _ = _ := by
           rw [hinc (n+1),hinc n,← sum_sub_distrib]
           refine sum_congr rfl fun j _ => ?_
           simp only [Nat.cast_succ,t,add_sub_add_left_eq_sub]
  have he : t*(t+1)*K+M = ∑ j ∈ range (d : ℕ), F (offset d r j) := by
    rw [hK,mul_sum]
    exact (sum_add_distrib ..).symm
  rw [he]
  have ht : 1 ≤ t := by dsimp [t]; linarith only [Nat.cast_nonneg (R := ℝ) n]
  constructor
  · exact sum_le_sum fun j hj => (centered_log_bounds ht (offset_bounds hr (mem_range.mp hj))).1
  · exact sum_le_sum fun j hj => (centered_log_bounds ht (offset_bounds hr (mem_range.mp hj))).2

#print axioms residue_curvature_bounds
#print axioms block_curvature
#print axioms block_curvature_bounds

end GaloisForLFunctions.SignedArithmeticCorrespondences
