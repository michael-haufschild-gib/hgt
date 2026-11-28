import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting.Endpoints

/-! # Classification of coassociative isometric divisor kernels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting

/-- Each occupied left factor is entirely left-facing, and each occupied
right factor entirely right-facing, with their common vacuum phase. -/
def endpoints (F : Kernel) := ∀ a b, F a b≠0 → F a 1=F 1 1 ∧ F 1 b=F 1 1

private theorem smaller_left (a b : ℕ+) (hb : b≠1) : a.val < (a*b).val := by
  have ne : b.val≠1 := fun h => hb (PNat.coe_injective h)
  have pos := b.pos
  simpa only [Nat.mul_one,PNat.mul_coe] using Nat.mul_lt_mul_of_pos_left (show 1<b.val by omega) a.pos

private theorem normalize_endpoint {F : Kernel} (hn : normalized F) {x : ℂ} (h : x=F 1 1) :
    ‖x‖^2=1 := by rw [h,vacuum_unit F hn]

private theorem vacuum_ne_zero {F : Kernel} (hn : normalized F) : F 1 1≠0 := by
  intro e
  have h := vacuum_unit F hn
  simp only [e,norm_zero,zero_pow (two_ne_zero : (2:ℕ)≠0),zero_ne_one] at h

private theorem necessity (F : Kernel) (hn : normalized F) (hc : coassociative F) :
    endpoints F := by
  have induction_step (n : ℕ) : ∀ (a b : ℕ+), (a*b).val=n → F a b≠0 →
      F a 1=F 1 1 ∧ F 1 b=F 1 1 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b size nz
      by_cases ha : a=1
      · subst a
        exact ⟨rfl,right_endpoint F hc b nz⟩
      by_cases hb : b=1
      · subst b
        exact ⟨left_endpoint F hc a nz,rfl⟩
      have right_total : F 1 (a*b)=0 := by
        by_contra h
        have eqn := exclusive F hn (one_mul (a*b))
          (normalize_endpoint hn (right_endpoint F hc (a*b) h)) nz
        exact ha (congrArg Prod.fst eqn)
      have right_a : F 1 a=0 := by
        have h := hc 1 a b
        rw [one_mul,right_total,zero_mul] at h
        exact (mul_eq_zero.mp h).resolve_left nz
      have bridge : F a 1=F 1 b := by
        have h := hc a 1 b
        rw [mul_one,one_mul] at h
        exact mul_left_cancel₀ nz h
      have left_nonzero : F a 1≠0 := by
        intro zero
        obtain ⟨u,v,prod,uv⟩ := occupied F hn a
        have hu : u≠1 := by
          rintro rfl
          rw [one_mul] at prod
          exact uv (by rw [prod,right_a])
        have hv : v≠1 := by
          rintro rfl
          rw [mul_one] at prod
          exact uv (by rw [prod,zero])
        have relation := hc u v b
        rw [prod] at relation
        have nzprod : F u (v*b)*F v b≠0 := by rw [←relation]; exact mul_ne_zero nz uv
        have vb := (mul_ne_zero_iff.mp nzprod).2
        have a_small : a.val<n := (smaller_left a b hb).trans_eq size
        have v_small : v.val<a.val := by
          rw [←prod,mul_comm u v]
          exact smaller_left v u hu
        have vb_small : (v*b).val<n := by
          rw [←size]
          exact Nat.mul_lt_mul_of_pos_right v_small b.pos
        have right_v := (ih a.val a_small u v (congrArg PNat.val prod) uv).2
        have left_v := (ih (v*b).val vb_small v b rfl vb).1
        have left_nz : F v 1≠0 := by rw [left_v]; exact vacuum_ne_zero hn
        have conflict := exclusive F hn (show (1:ℕ+)*v=v*1 by rw [one_mul,mul_one])
          (normalize_endpoint hn right_v) left_nz
        exact hv (congrArg Prod.fst conflict)
      have left := left_endpoint F hc a left_nonzero
      exact ⟨left,bridge.symm.trans left⟩
  exact fun a b nz => induction_step _ a b rfl nz

private theorem sufficient (F : Kernel) (hn : normalized F) (h : endpoints F) : coassociative F := by
  intro a b c
  by_cases unit : b=1
  · subst b
    rw [mul_one,one_mul]
    by_cases nz : F a c=0
    · rw [nz,zero_mul,zero_mul]
    · rw [(h a c nz).1,(h a c nz).2]
  have left : F (a*b) c * F a b=0 := by
    by_contra nz
    obtain ⟨outer,inner⟩ := mul_ne_zero_iff.mp nz
    have eqn := exclusive F hn (mul_one (a*b)) (normalize_endpoint hn (h (a*b) c outer).1) inner
    exact unit (congrArg Prod.snd eqn)
  have right : F a (b*c) * F b c=0 := by
    by_contra nz
    obtain ⟨outer,inner⟩ := mul_ne_zero_iff.mp nz
    have eqn := exclusive F hn (one_mul (b*c)) (normalize_endpoint hn (h a (b*c) outer).2) inner
    exact unit (congrArg Prod.fst eqn)
  exact left.trans right.symm

/-- Coassociativity and global isometry are jointly equivalent to unit shell
mass with deterministic endpoint factors on every nonzero coefficient. -/
theorem classification (F : Kernel) : isometric F ∧ coassociative F ↔ normalized F ∧ endpoints F := by
  rw [isometric_iff]
  exact ⟨fun h => ⟨h.1,necessity F h.1 h.2⟩,fun h => ⟨h.1,sufficient F h.1 h.2⟩⟩

#print axioms classification

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting
