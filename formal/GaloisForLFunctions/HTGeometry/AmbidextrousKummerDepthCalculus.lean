import GaloisForLFunctions.HTGeometry.ConstitutiveAmbidextrousKummerSelection

/-!
# The ambidextrous Kummer depth calculus

Kummer depth carries two canonical maps between the cyclic charge groups.  Restriction
`ZMod m → ZMod n` for `n ∣ m` is the quotient, and it is flat for every integer charge.  Covariant
inclusion `ZMod n → ZMod m`, the map that sends an `n`-th root of unity to itself as an `m`-th root,
multiplies representatives by `m / n`, and it is *not* flat.  The mismatch is a crossed cocycle in
the depth tower, and its cofinal vanishing forces the charge to be zero.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## The two canonical depth maps -/

/-- Restriction of Kummer depth. -/
def depthRestriction {n m : ℕ} (h : n ∣ m) : ZMod m →+* ZMod n := ZMod.castHom h (ZMod n)

@[simp] theorem depthRestriction_intCast {n m : ℕ} (h : n ∣ m) (q : ℤ) :
    depthRestriction h (q : ZMod m) = (q : ZMod n) :=
  map_intCast (ZMod.castHom h (ZMod n)) q

/-- **Restriction is flat**: the restricted charge class is the charge class. -/
theorem depthRestriction_flat {n m : ℕ} (h : n ∣ m) (q : ℤ) :
    depthRestriction h (q : ZMod m) = (q : ZMod n) :=
  depthRestriction_intCast h q

/-- Covariant inclusion of Kummer depth: an `n`-th root of unity read as an `m`-th root. -/
def depthInclusion {n m : ℕ} (h : n ∣ m) : ZMod n →+ ZMod m :=
  ZMod.lift n ⟨(AddMonoidHom.mulLeft ((m / n : ℕ) : ZMod m)).comp (Int.castAddHom (ZMod m)), by
    have hmn : (m / n) * n = m := Nat.div_mul_cancel h
    show ((m / n : ℕ) : ZMod m) * ((n : ℤ) : ZMod m) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, hmn, ZMod.natCast_self]⟩

@[simp] theorem depthInclusion_intCast {n m : ℕ} (h : n ∣ m) (q : ℤ) :
    depthInclusion h (q : ZMod n) = ((m / n : ℕ) : ZMod m) * (q : ZMod m) := by
  rw [depthInclusion, ZMod.lift_coe]
  rfl

/-- **The two laws compose**: restriction is functorial along the depth tower. -/
theorem depthRestriction_comp {n m ℓ : ℕ} (h₁ : n ∣ m) (h₂ : m ∣ ℓ) (x : ZMod ℓ) :
    depthRestriction h₁ (depthRestriction h₂ x) = depthRestriction (h₁.trans h₂) x := by
  obtain ⟨q, rfl⟩ := ZMod.intCast_surjective (n := ℓ) x
  simp

theorem div_mul_div_of_dvd_dvd {n m ℓ : ℕ} (h₁ : n ∣ m) (h₂ : m ∣ ℓ) :
    (ℓ / m) * (m / n) = ℓ / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : m = 0 := Nat.eq_zero_of_zero_dvd h₁
    obtain rfl : ℓ = 0 := Nat.eq_zero_of_zero_dvd h₂
    simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : ℓ = 0 := Nat.eq_zero_of_zero_dvd h₂
    simp
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  rw [Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hn,
    show n * a * b = n * (a * b) from by ring, Nat.mul_div_cancel_left _ hn, mul_comm]

/-- **The two laws compose**: covariant inclusion is functorial along the depth tower. -/
theorem depthInclusion_comp {n m ℓ : ℕ} (h₁ : n ∣ m) (h₂ : m ∣ ℓ) (x : ZMod n) :
    depthInclusion h₂ (depthInclusion h₁ x) = depthInclusion (h₁.trans h₂) x := by
  obtain ⟨q, rfl⟩ := ZMod.intCast_surjective (n := n) x
  have hc : ((m / n : ℕ) : ZMod m) * ((q : ℤ) : ZMod m)
      = ((((m / n : ℕ) : ℤ) * q : ℤ) : ZMod m) := by
    rw [Int.cast_mul, Int.cast_natCast]
  rw [depthInclusion_intCast h₁, hc, depthInclusion_intCast h₂, depthInclusion_intCast,
    Int.cast_mul, Int.cast_natCast, ← mul_assoc, ← Nat.cast_mul,
    div_mul_div_of_dvd_dvd h₁ h₂]

/-! ## The ambidextrous defect -/

/-- Defect of the covariant inclusion law at one depth change. -/
def ambidextrousDefect {n m : ℕ} (h : n ∣ m) (q : ℤ) : ZMod m :=
  (q : ZMod m) - depthInclusion h (q : ZMod n)

theorem ambidextrousDefect_eq {n m : ℕ} (h : n ∣ m) (q : ℤ) :
    ambidextrousDefect h q = (q : ZMod m) - ((m / n : ℕ) : ZMod m) * (q : ZMod m) := by
  rw [ambidextrousDefect, depthInclusion_intCast]

/-- **The crossed defect cocycle.**  The defect of a composite depth change is the outer defect
plus the covariant transport of the inner one. -/
theorem ambidextrousDefect_cocycle {n m ℓ : ℕ} (h₁ : n ∣ m) (h₂ : m ∣ ℓ) (q : ℤ) :
    ambidextrousDefect (h₁.trans h₂) q
      = ambidextrousDefect h₂ q + depthInclusion h₂ (ambidextrousDefect h₁ q) := by
  rw [ambidextrousDefect, ambidextrousDefect, ambidextrousDefect, map_sub,
    depthInclusion_comp h₁ h₂]
  abel

/-- At a doubling the general defect is the doubling defect of the finite selector. -/
theorem ambidextrousDefect_doubling {n : ℕ} (hn : 0 < n) (q : ℤ) :
    ambidextrousDefect (⟨2, by ring⟩ : n ∣ 2 * n) q = ambidextrousDoublingDefect n q := by
  have hdiv : (2 * n) / n = 2 := by
    exact Nat.mul_div_cancel _ hn
  rw [ambidextrousDefect_eq, ambidextrousDoublingDefect, hdiv]
  norm_num

/-! ## Exact selection and reconstruction -/

theorem ambidextrousDefect_zero {n m : ℕ} (h : n ∣ m) : ambidextrousDefect h 0 = 0 := by
  rw [ambidextrousDefect_eq]
  simp

/-- **Theorem 3.1 — exact selection.**  Charge zero, universal ambidextrous flatness, doubling
flatness, and eventual doubling flatness are the same condition. -/
theorem ambidextrousDefect_tfae (q : ℤ) :
    List.TFAE
      [ q = 0,
        ∀ (n m : ℕ) (h : n ∣ m), ambidextrousDefect h q = 0,
        ∀ n : ℕ, 0 < n → ambidextrousDoublingDefect n q = 0,
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ambidextrousDoublingDefect n q = 0 ] := by
  tfae_have 1 → 2 := by
    rintro rfl n m h
    exact ambidextrousDefect_zero h
  tfae_have 2 → 3 := by
    intro h2 n hn
    rw [← ambidextrousDefect_doubling hn q]
    exact h2 n (2 * n) _
  tfae_have 3 → 4 := fun h3 => ⟨1, fun n hn => h3 n hn⟩
  tfae_have 4 → 1 := by
    rintro ⟨N, hN⟩
    by_contra hq
    set n := max N (q.natAbs + 1) with hn
    exact ambidextrousDoublingDefect_ne_zero hq
      (lt_of_lt_of_le (Nat.lt_add_one q.natAbs) (le_max_right _ _))
      (hN n (le_max_left _ _))
  tfae_finish

theorem intCast_inj_of_natAbs_lt {n : ℕ} {a b : ℤ} (ha : a.natAbs < n) (hb : b.natAbs < n)
    (h : (a : ZMod (2 * n)) = (b : ZMod (2 * n))) : a = b := by
  have hzero : ((a - b : ℤ) : ZMod (2 * n)) = 0 := by
    push_cast
    rw [h, sub_self]
  have hdvd : ((2 * n : ℕ) : ℤ) ∣ (a - b) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.2 hne
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hsub
  simp only [Int.natAbs_natCast] at hle
  have : (a - b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_sub_le a b
  omega

/-- **Corollary 3.2 — defect reconstruction.**  The cofinal doubling-defect family determines the
integer charge. -/
theorem eq_of_doublingDefect_eq {q r : ℤ}
    (h : ∀ n : ℕ, ambidextrousDoublingDefect n q = ambidextrousDoublingDefect n r) : q = r := by
  set n := max q.natAbs r.natAbs + 1 with hn
  have hq : q.natAbs < n := by omega
  have hr : r.natAbs < n := by omega
  have hn0 : (-q : ℤ).natAbs < n := by simpa using hq
  have hr0 : (-r : ℤ).natAbs < n := by simpa using hr
  have hcast : ((-q : ℤ) : ZMod (2 * n)) = ((-r : ℤ) : ZMod (2 * n)) := by
    have hh := h n
    rw [ambidextrousDoublingDefect_eq, ambidextrousDoublingDefect_eq] at hh
    push_cast
    exact hh
  have := intCast_inj_of_natAbs_lt hn0 hr0 hcast
  linarith

/-- The centered representative of the doubling defect is the negated charge. -/
theorem doublingDefect_reconstructs {n : ℕ} {q : ℤ} (hq : q.natAbs < n) :
    ambidextrousDoublingDefect n q = ((-q : ℤ) : ZMod (2 * n)) ∧ (-q : ℤ).natAbs < n := by
  refine ⟨?_, by simpa using hq⟩
  rw [ambidextrousDoublingDefect_eq]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
