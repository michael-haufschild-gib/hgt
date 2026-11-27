import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Filling.PhaseAlignment

/-! # An explicit replica order for simultaneous phase filling -/
open Real Finset
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

private def discount := min (1/2:ℝ) (coherentFraction/2)
private theorem discount_pos : 0 < discount := lt_min (by norm_num) (half_pos coherentFraction_pos)

/-- A polynomial order is sufficient because each occupation coordinate
lies between zero and q, while the aligned trace threshold decays geometrically. -/
def alignmentOrder (D : ℕ) (ε : ℝ) :=
  let η := ε^2/(2*(D:ℝ))
  D*(⌈((D:ℝ)+1)/(discount*η^2)⌉₊+1)

private theorem occupancy_card_le (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    Fintype.card (ReplicaMultiplicityIndex I q) ≤ (q+1)^Fintype.card I := by
  let code (p : ReplicaMultiplicityIndex I q) (i : I) : Fin (q+1) := ⟨p.val i,Nat.lt_succ_of_le
    ((single_le_sum (f:=p.val) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans_eq
      (mem_piAntidiag.mp p.property).1)⟩
  have hinj : Function.Injective code := by
    intro p z h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  simpa only [Fintype.card_fun,Fintype.card_fin] using Fintype.card_le_of_injective code hinj

private theorem geometric_decay {η : ℝ} (hη : 0 ≤ η) (h₁ : η ≤ 1) (m : ℕ) :
    (m:ℝ)*η*(1-η)^m ≤ 1 := by
  have hx : 1-η ≤ exp (-η) := by linarith only [add_one_le_exp (-η)]
  have h := pow_le_pow_left₀ (sub_nonneg.mpr h₁) hx m
  rw [←exp_nat_mul,mul_neg,exp_neg] at h
  have he : (m:ℝ)*η ≤ exp ((m:ℝ)*η) := by linarith only [add_one_le_exp ((m:ℝ)*η)]
  exact (mul_le_mul he h (pow_nonneg (sub_nonneg.mpr h₁) _) (exp_pos _).le).trans_eq
    (mul_inv_cancel₀ (exp_pos _).ne')

/-- This order meets the strict Ingham price at every chordal tolerance
through one, including on a single-level spectrum. -/
theorem alignmentOrder_price (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I] {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    let D := Fintype.card I
    let q := alignmentOrder D ε
    (Fintype.card (ReplicaMultiplicityIndex I q):ℝ)*(1-ε^2/(2*(D:ℝ)))^(2*q) < coherentFraction := by
  intro D q
  let η := ε^2/(2*(D:ℝ))
  let m := ⌈((D:ℝ)+1)/(discount*η^2)⌉₊+1
  have hD : 1 ≤ D := Fintype.card_pos
  have hD' : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hη : 0 < η := by dsimp only [η]; positivity
  have hη₁ : η ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [pow_le_one₀ hε.le hε₁ (n:=2),hD']
  have hmp : 0 < m := Nat.succ_pos _
  have hm : ((D:ℝ)+1)/(discount*η^2) ≤ (m:ℝ) :=
    (Nat.le_ceil _).trans (by dsimp only [m]; push_cast; linarith)
  have hm₁ : D*m+1 ≤ (D+1)*m := by rw [Nat.add_mul,one_mul]; omega
  have hg : ((q:ℝ)+1) ≤ discount*((m:ℝ)*η)^2 := by
    have hq : (q:ℝ)+1 ≤ ((D:ℝ)+1)*m := by exact_mod_cast hm₁
    have hmul := (div_le_iff₀ (mul_pos discount_pos (sq_pos_of_pos hη))).mp hm
    exact hq.trans ((mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg m)).trans_eq (by ring))
  have hpow := geometric_decay hη.le hη₁ m
  have hx : 0 ≤ (1-η)^m := pow_nonneg (sub_nonneg.mpr hη₁) _
  have ht : ((q:ℝ)+1)*(1-η)^(2*m) ≤ discount := by
    rw [Nat.mul_comm 2 m,pow_mul]
    apply (mul_le_mul_of_nonneg_right hg (sq_nonneg _)).trans
    rw [mul_assoc,←mul_pow]
    exact mul_le_of_le_one_right discount_pos.le (pow_le_one₀
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hη.le) hx) hpow)
  have hcard : (Fintype.card (ReplicaMultiplicityIndex I q):ℝ) ≤ ((q:ℝ)+1)^D := by
    exact_mod_cast occupancy_card_le I q
  have he : 2*q=2*m*D := by change 2*(D*m)=_; ring
  have hd₁ : discount ≤ 1 := (min_le_left ..).trans (by norm_num)
  have hdκ : discount < coherentFraction := (min_le_right ..).trans_lt (half_lt_self coherentFraction_pos)
  change _*(1-η)^(2*q) < _
  apply (mul_le_mul_of_nonneg_right hcard (pow_nonneg (sub_nonneg.mpr hη₁) _)).trans_lt
  rw [he,pow_mul,←mul_pow]
  have hbase : 0 ≤ ((q:ℝ)+1)*(1-η)^(2*m) := by positivity
  exact (pow_le_pow_left₀ hbase ht D).trans_lt ((show discount^D ≤ discount by
    simpa only [pow_one] using pow_le_pow_of_le_one discount_pos.le hd₁ hD).trans_lt hdκ)

#print axioms alignmentOrder_price
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
