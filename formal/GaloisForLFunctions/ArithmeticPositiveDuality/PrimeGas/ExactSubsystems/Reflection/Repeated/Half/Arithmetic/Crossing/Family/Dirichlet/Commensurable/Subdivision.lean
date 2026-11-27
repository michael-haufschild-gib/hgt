import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Separation

/-! # Persistent thermal readings under rational subdivision -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Set

/-- Orders that remain forced at every positive integral subdivision. -/
def persistent (t : ℝ) : Set ℝ :=
  {u | 0<u ∧ ∀ d : ℕ, 0<d → Forces (t/d) (u/d)}

private theorem subdivides {R : ℝ → ℝ → Prop}
    (grow : ∀ {x y : ℝ}, R x y → ∀ j : ℕ, R (x*j) (y*j))
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (dvd : a ∣ b) {t u : ℝ}
    (h : R (t/b) (u/b)) : R (t/a) (u/a) := by
  obtain ⟨k,eq⟩ := dvd
  have hk : 0<k := by apply Nat.pos_of_ne_zero; rintro rfl; simp [eq] at hb
  have id (x : ℝ) : x/b*k=x/a := by
    rw [eq,Nat.cast_mul]
    field_simp [(Nat.cast_pos.mpr ha : 0<(a : ℝ)).ne',(Nat.cast_pos.mpr hk : 0<(k : ℝ)).ne']
  simpa only [id] using grow h k

/-- Integer subdivisions suffice because every positive rational scale is a
positive integer multiple of a reciprocal integer. -/
private theorem all_scales {R : ℝ → ℝ → Prop}
    (grow : ∀ {x y : ℝ}, R x y → ∀ j : ℕ, R (x*j) (y*j)) (t u : ℝ) :
    (∀ d : ℕ, 0<d → R (t/d) (u/d)) ↔
    ∀ q : ℚ, 0<q → R ((q : ℝ)*t) ((q : ℝ)*u) := by
  constructor
  · intro all q hq
    obtain ⟨a,b,_,hb,rep⟩ := natural_ratio q hq
    have id (x : ℝ) : x/b*a=(q : ℝ)*x := by
      rw [← rep]
      field_simp [(Nat.cast_pos.mpr hb : 0<(b : ℝ)).ne']
    simpa only [id] using grow (all b hb) a
  · intro all d hd
    have h := all ((d : ℚ)⁻¹) (inv_pos.mpr (Nat.cast_pos.mpr hd))
    simpa only [Rat.cast_inv,Rat.cast_natCast,div_eq_inv_mul] using h

theorem persistent_iff_rational {t u : ℝ} (hu : 0<u) :
    u ∈ persistent t ↔ ∀ q : ℚ, 0<q → Forces ((q : ℝ)*t) ((q : ℝ)*u) :=
  (and_iff_right hu).trans (all_scales (R := Forces) forces_dilate t u)

private theorem self_scale (t : ℝ) (d : ℕ) (hd : 0<d) {u : ℝ}
    (h : Forces (t/d) (u/d)) : Forces t u := by
  simpa only [div_mul_cancel₀ _ (Nat.cast_pos.mpr hd : 0<(d : ℝ)).ne'] using forces_dilate h d

/-- The finite least spectrum at the original order supplies a common
denominator eliminating every target that ever disappears. -/
theorem subdivision_stabilizes {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ D : ℕ, 0<D ∧ ∀ k : ℕ, 0<k → ∀ u : ℝ, 0<u →
      (Forces (t/↑(D*k)) (u/↑(D*k)) ↔ u ∈ persistent t) := by
  classical
  let removed := consequences t \ persistent t
  have fin : removed.Finite := (attainable_finite (least_spectrum ht res)).subset Set.sdiff_subset
  letI : Fintype removed := fin.fintype
  have missing (u : removed) : ∃ d : ℕ, 0<d ∧ ¬Forces (t/d) (u.val/d) := by
    by_contra! all
    exact u.property.2 ⟨u.property.1.1,all⟩
  choose d pos fail using missing
  let D := ∏ u, d u
  have dp : 0<D := Finset.prod_pos (fun u _ => pos u)
  refine ⟨D,dp,fun k hk u hu => ⟨fun force => ?_,fun mem => mem.2 (D*k) (mul_pos dp hk)⟩⟩
  by_contra absent
  let v : removed := ⟨u,⟨hu,self_scale t (D*k) (mul_pos dp hk) force⟩,absent⟩
  have dvd : d v ∣ D := Finset.dvd_prod_of_mem _ (mem_univ v)
  exact fail v (subdivides (R := Forces) forces_dilate (pos v) (mul_pos dp hk)
    (dvd.trans (dvd_mul_right D k)) force)

private theorem subdivided_spectrum {t : ℝ} (ht : 0<t) (res : Resonant t) {d : ℕ} (hd : 0<d)
    (eq : ∀ u : ℝ, 0<u → (Forces (t/d) (u/d) ↔ u ∈ persistent t)) :
    ∃ S : Set ℝ, Attainable S ∧ t/d ∈ S ∧ ∀ u : ℝ, 0<u → (u/d ∈ S ↔ u ∈ persistent t) := by
  have dp := (Nat.cast_pos.mpr hd : 0<(d : ℝ))
  have hp := div_pos ht dp
  have rs : Resonant (t/d) := (resonant_nat_iff (m := d) hp hd).mp
    (by rw [div_mul_cancel₀ _ dp.ne']; exact res)
  refine ⟨consequences (t/d),least_spectrum hp rs,⟨hp,fun _ _ h => h⟩,fun u hu => ?_⟩
  exact ⟨fun hit => (eq u hu).mp hit.2, fun hit => ⟨div_pos hu dp,(eq u hu).mpr hit⟩⟩

theorem persistent_spectra {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ D : ℕ, 0<D ∧ ∀ k : ℕ, 0<k → ∃ S : Set ℝ, Attainable S ∧ t/↑(D*k) ∈ S ∧
      ∀ u : ℝ, 0<u → (u/↑(D*k) ∈ S ↔ u ∈ persistent t) := by
  obtain ⟨D,pos,stable⟩ := subdivision_stabilizes ht res
  exact ⟨D,pos,fun k hk => subdivided_spectrum (d := D*k) ht res (mul_pos pos hk) (stable k hk)⟩

/-- One sign works simultaneously at every rational subdivision. Two
denominators always have a common refinement, so two incompatible sign
failures would contradict forcing there. -/
theorem persistent_signed {t u : ℝ} (ht : 0<t) (hu : 0<u) :
    u ∈ persistent t ↔
      (∀ q : ℚ, 0<q → kernel ((q : ℝ)*t) ≤ kernel ((q : ℝ)*u)) ∨
      (∀ q : ℚ, 0<q → kernel ((q : ℝ)*t) ≤ kernel (-((q : ℝ)*u))) := by
  let plus (x y : ℝ) := kernel x ≤ kernel y
  let minus (x y : ℝ) := kernel x ≤ kernel (-y)
  have fg {x y : ℝ} (h : plus x y) (j : ℕ) : plus (x*j) (y*j) := kernel_dilate h j
  have bg {x y : ℝ} (h : minus x y) (j : ℕ) : minus (x*j) (y*j) := by
    change kernel (x*j) ≤ kernel (-(y*j))
    rw [← neg_mul]
    exact kernel_dilate h j
  constructor
  · intro mem
    by_cases all : ∀ d : ℕ, 0<d → plus (t/d) (u/d)
    · exact Or.inl ((all_scales (R := plus) fg t u).mp all)
    · push Not at all
      obtain ⟨a,ha,fail⟩ := all
      refine Or.inr ((all_scales (R := minus) bg t u).mp (fun b hb => ?_))
      have ap : 0<a*b := mul_pos ha hb
      have dp := (Nat.cast_pos.mpr ap : 0<(↑(a*b) : ℝ))
      have h := (forces_iff (div_pos ht dp) (div_pos hu dp)).mp (mem.2 (a*b) ap)
      rcases h with p | m
      · exact (fail (subdivides (R := plus) fg ha ap (dvd_mul_right a b) p)).elim
      · exact subdivides (R := minus) bg hb ap (dvd_mul_left b a) m
  · intro h
    apply (persistent_iff_rational hu).mpr
    intro q hq
    have qp := (Rat.cast_pos.mpr hq : 0<(q : ℝ))
    exact (forces_iff (mul_pos qp ht) (mul_pos qp hu)).mpr (h.imp (fun p => p q hq) (fun m => m q hq))

#print axioms persistent_iff_rational
#print axioms subdivision_stabilizes
#print axioms persistent_spectra
#print axioms persistent_signed

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
