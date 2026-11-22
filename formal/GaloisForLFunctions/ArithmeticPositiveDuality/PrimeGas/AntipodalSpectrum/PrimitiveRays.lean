import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.WindingLattice

/-!
# Occupation basis on the rejected sector

A reduced ratio determines a ray of common integer multiples. A nonzero
winding determines both its exponent and its orientation. These coordinates
separate the heat weight into a doubled radial heat and a geometric weight.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open CopyExchange DyadicAperture.Binary
open scoped Classical

abbrev Missing (m : ℕ) := {k : ℕ // ¬m ∣ k}

private def axis (a b : ℕ+) (rev : Bool) := cond rev b a
private def orient (rev : Bool) (d : ℝ) := cond rev (-d) d

def ray (a b : ℕ+) (rev : Bool) (k : ℕ) (n : ℕ+) :=
  pair ((axis a b rev)^k*n) ((axis b a rev)^k*n)

private theorem energy_injective : Function.Injective energy := by
  intro a b h
  have he := congrArg Real.exp h
  rw [energy,energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) he)

private theorem gap_ne {a b : ℕ+} (h : a ≠ b) : gap a b ≠ 0 :=
  sub_ne_zero.mpr (fun he => h (energy_injective he))

private theorem energy_pow (a : ℕ+) (k : ℕ) : energy (a^k) = (k:ℝ)*energy a := by
  simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]

private theorem gap_pow (a b : ℕ+) (k : ℕ) : gap (a^k) (b^k) = (k:ℝ)*gap a b := by
  rw [gap,energy_pow,energy_pow,gap,mul_sub]

private theorem ray_gap (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    gap (ray a b r k n false) (ray a b r k n true) = (k:ℝ)*orient r (gap a b) := by
  cases r <;> simp only [ray,pair,axis,orient,cond_false,cond_true,gap,energy_mul,energy_pow] <;> ring

private theorem reduced_ray {a b u v : ℕ+} (hc : a.Coprime b) (h : gap u v = gap a b) :
    ∃ n : ℕ+, u = a*n ∧ v = b*n := by
  have he : u*b = v*a := energy_injective (by rw [energy_mul,energy_mul]; unfold gap at h; linarith only [h])
  have hm : u.val*b.val = v.val*a.val := congrArg PNat.val he
  have hdiv : a.val ∣ u.val*b.val := ⟨v.val,hm.trans (Nat.mul_comm _ _)⟩
  obtain ⟨n,hu⟩ := (PNat.coprime_coe.mpr hc).dvd_of_dvd_mul_right hdiv
  have hn : n ≠ 0 := fun hz => u.ne_zero (by simpa only [hz,Nat.mul_zero] using hu)
  refine ⟨⟨n,Nat.pos_of_ne_zero hn⟩,PNat.coe_injective hu,PNat.coe_injective ?_⟩
  apply Nat.eq_of_mul_eq_mul_left a.pos
  change a.val*v.val = a.val*(b.val*n)
  calc
    a.val*v.val = u.val*b.val := (Nat.mul_comm _ _).trans hm.symm
    _ = a.val*(b.val*n) := by rw [hu]; ac_rfl

private theorem pow_coprime {a b : ℕ+} (hc : a.Coprime b) (k : ℕ) : (a^k).Coprime (b^k) :=
  PNat.coprime_coe.mp ((PNat.coprime_coe.mpr hc).pow k k)

private theorem realize {a b : ℕ+} (hc : a.Coprime b) (x : Word) (k : ℕ)
    (hx : signed (gap (x false) (x true)) k (gap a b)) :
    ∃ (r : Bool) (n : ℕ+), ray a b r k n = x := by
  rcases hx with h | h
  · obtain ⟨n,hf,ht⟩ := reduced_ray (pow_coprime hc k) (h.trans (gap_pow a b k).symm)
    exact ⟨false,n,funext fun i => by cases i; exact hf.symm; exact ht.symm⟩
  · have he : gap (x true) (x false) = (k:ℝ)*gap a b := by unfold gap at *; linarith only [h]
    obtain ⟨n,ht,hf⟩ := reduced_ray (pow_coprime hc k) (he.trans (gap_pow a b k).symm)
    exact ⟨true,n,funext fun i => by cases i; exact hf.symm; exact ht.symm⟩

private theorem abs_orient (r : Bool) (d : ℝ) : |orient r d| = |d| := by cases r <;> simp [orient]

private theorem orient_inj {d : ℝ} (hd : d ≠ 0) : Function.Injective (fun r => orient r d) := by
  intro r s h
  cases r <;> cases s
  · rfl
  · exact (hd (by change d = -d at h; linarith only [h])).elim
  · exact (hd (by change -d = d at h; linarith only [h])).elim
  · rfl

private theorem ray_injective (m : ℕ) {a b : ℕ+} (hd : a ≠ b) : Function.Injective
    (fun p : Bool × (Missing m × ℕ+) => ray a b p.1 p.2.1.val p.2.2) := by
  rintro ⟨r,k,n⟩ ⟨s,l,u⟩ eq
  have hg := congrArg (fun x : Word => gap (x false) (x true)) eq
  change gap (ray a b r k.val n false) (ray a b r k.val n true) =
    gap (ray a b s l.val u false) (ray a b s l.val u true) at hg
  rw [ray_gap,ray_gap] at hg
  have ha := congrArg abs hg
  simp only [abs_mul,abs_orient,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ k.val),
    abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ l.val)] at ha
  have hkl : k = l := Subtype.ext (Nat.cast_injective (R := ℝ) (mul_right_cancel₀ (abs_ne_zero.mpr (gap_ne hd)) ha))
  subst l
  have hn : k.val ≠ 0 := fun h => k.property (h ▸ dvd_zero _)
  have hrs := orient_inj (gap_ne hd) (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn) hg)
  subst s
  have hfirst : (axis a b r)^k.val*n = (axis a b r)^k.val*u := congrArg (fun x : Word => x false) eq
  exact congrArg (fun v => (r,k,v)) (mul_left_cancel hfirst)

/-- Every rejected occupation is uniquely a sign, a missing winding, and a radial integer. -/
theorem rejected_basis (t : {t : ℝ // t ∈ exceptional}) : ∃ (a b : ℕ+) (m : ℕ),
    a.Coprime b ∧ a ≠ b ∧ 1 < m ∧ (∃ j : ℕ, m = 2^j) ∧
      ∃ e : (Bool × (Missing m × ℕ+)) ≃ {x // rejected t.val x},
        ∀ p, (e p).val = ray a b p.1 p.2.1.val p.2.2 := by
  obtain ⟨a,b,m,hc,hd,hm,hpow,hclass⟩ := rejected_lattice t
  have accepted (r : Bool) (k : Missing m) (n : ℕ+) : rejected t.val (ray a b r k.val n) := by
    apply (hclass _).mpr
    refine ⟨k.val,k.property,?_⟩
    rw [ray_gap]
    cases r
    · exact Or.inl rfl
    · exact Or.inr (mul_neg _ _)
  let f (p : Bool × (Missing m × ℕ+)) : {x // rejected t.val x} :=
    ⟨ray a b p.1 p.2.1.val p.2.2,accepted _ _ _⟩
  have hi : Function.Injective f := fun _ _ he => ray_injective m hd (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨k,hk,hg⟩ := (hclass x).mp hx
    obtain ⟨r,n,he⟩ := realize hc x k hg
    exact ⟨(r,⟨k,hk⟩,n),Subtype.ext he⟩
  exact ⟨a,b,m,hc,hd,hm,hpow,Equiv.ofBijective f ⟨hi,hs⟩,fun _ => rfl⟩

private theorem heat_pow (s : ℂ) (a : ℕ+) (k : ℕ) : heat s (a^k) = (heat s a)^k := by
  induction k with
  | zero => simp [heat,energy]
  | succ k ih => rw [pow_succ,heat_mul,ih,pow_succ]

/-- Both orientations occupy the same total energy shell. -/
theorem ray_product (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    ray a b r k n false * ray a b r k n true = (a*b)^k*n^2 := by
  cases r <;> simp only [ray,pair,axis,cond_false,cond_true,mul_pow,pow_two] <;> ac_rfl

/-- Each ray has the ordinary radial partition at doubled inverse temperature. -/
theorem ray_heat (s : ℂ) (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    wordHeat s (ray a b r k n) = (heat s (a*b))^k*heat (2*s) n := by
  cases r <;> simp only [wordHeat,Fintype.prod_bool,ray,pair,axis,cond_true,cond_false,heat_mul,heat_pow,
    mul_pow,two_mul,heat_add] <;> ring

#print axioms rejected_basis
#print axioms ray_product
#print axioms ray_heat

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
