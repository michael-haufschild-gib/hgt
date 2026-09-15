import GaloisForLFunctions.RHTower.EulerDeletionCoprimeHeadSubpower
import GaloisForLFunctions.RHTower.EulerDeletionMobiusPrimitiveEnergy
/-!
# Subpower remainder of all exact-gcd Möbius residue heads

For each positive gcd, retain the literal cofactor coprimality masks and every
within-block affine offset. Completing the inner Möbius floor column gives a
prime-supported count. Its uniform small-power bound and the physical inverse
gcd scale control the sum of absolute head remainders over every gcd group.

Consequently the total head variation differs from the full harmonic-polynomial
variation by an arbitrarily small cutoff power. The leading harmonic coefficients
and the complete later tail are retained; this theorem supplies no RH bound for
those terms.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHTower.DeletionGcdHead
open Sieve DeletionCoprimeColumn

private def mu (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ)
private def maskedMu (r a : ℕ) : ℝ := if r.Coprime a then mu a else 0
private def pairForm (r Q : ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 Q, ∑ b ∈ Icc 1 Q,
    (if a.Coprime b then maskedMu r a*maskedMu r b else 0)*f a*g b

private theorem abs_mu_le (n : ℕ) : |mu n|≤1 := by
  dsimp [mu]
  exact_mod_cast (abs_moebius_le_one (n := n))

private theorem abs_maskedMu_le (r a : ℕ) : |maskedMu r a|≤1 := by
  unfold maskedMu
  split_ifs
  · exact abs_mu_le a
  · simp

private theorem mu_mul (r a : ℕ) : mu (r*a)=mu r*maskedMu r a := by
  by_cases h : r.Coprime a
  · simp only [maskedMu, if_pos h, mu,
      isMultiplicative_moebius.map_mul_of_coprime h, Int.cast_mul]
  · have hz : μ (r*a)=0 := moebius_eq_zero_of_not_squarefree
      (fun hs => h (Nat.coprime_of_squarefree_mul hs))
    simp [mu, maskedMu, h, hz]

private theorem pairForm_symm (r Q : ℕ) (f g : ℕ → ℝ) :
    pairForm r Q f g=pairForm r Q g f := by
  unfold pairForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : a.Coprime b
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (fun he => h he.symm)]; ring

private theorem pairForm_sub_square (r Q : ℕ) (f g : ℕ → ℝ) :
    pairForm r Q (fun a => f a-g a) (fun a => f a-g a) =
      pairForm r Q f f-2*pairForm r Q f g+pairForm r Q g g := by
  have h := pairForm_symm r Q f g
  have he : pairForm r Q (fun a => f a-g a) (fun a => f a-g a) =
      pairForm r Q f f-pairForm r Q f g-pairForm r Q g f+pairForm r Q g g := by
    simp only [pairForm, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, ← h]
  ring

private theorem pairForm_left_scale (r Q : ℕ) (f g : ℕ → ℝ) (c : ℝ) :
    pairForm r Q (fun a => c*f a) g=c*pairForm r Q f g := by
  unfold pairForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem truncated_column {Q t : ℕ} (htQ : t≤Q) (r a : ℕ) :
    (∑ b ∈ Icc 1 Q, (if a.Coprime b then maskedMu r b else 0)*(t/b : ℕ)) =
      ((primeSupportedIcc (r*a) t).card : ℝ) := by
  have hsum : (∑ b ∈ Icc 1 Q,
      (if a.Coprime b then maskedMu r b else 0)*(t/b : ℕ)) =
      ∑ b ∈ Icc 1 Q, (if (r*a).Coprime b then mu b else 0)*(t/b : ℕ) := by
    apply sum_congr rfl
    intro b _
    by_cases ha : a.Coprime b
    · by_cases hr : r.Coprime b
      · rw [if_pos ha, maskedMu, if_pos hr,
          if_pos (Nat.coprime_mul_iff_left.mpr ⟨hr,ha⟩)]
      · rw [if_pos ha, maskedMu, if_neg hr,
          if_neg (fun h => hr (Nat.coprime_mul_iff_left.mp h).1)]
    · rw [if_neg ha, if_neg (fun h => ha (Nat.coprime_mul_iff_left.mp h).2)]
  rw [hsum, ← complete_floor_column (r*a) t]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl htQ)
  intro b hb hnot
  have ht : t<b := by
    have hb1 := (mem_Icc.mp hb).1
    by_contra h
    exact hnot (mem_Icc.mpr ⟨hb1, by omega⟩)
  simp [Nat.div_eq_of_lt ht]

private theorem pairForm_floor_column {Q t : ℕ} (htQ : t≤Q)
    (r : ℕ) (f : ℕ → ℝ) :
    pairForm r Q f (fun b => (t/b : ℕ)) =
      ∑ a ∈ Icc 1 Q, maskedMu r a*f a*((primeSupportedIcc (r*a) t).card : ℝ) := by
  unfold pairForm
  apply Finset.sum_congr rfl
  intro a _
  rw [← truncated_column htQ r a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : a.Coprime b
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- The exact gcd-r residue group, parametrized by coprime cofactor pairs. -/
def residueQuadratic (r N k : ℕ) : ℝ :=
  (mu r)^2*pairForm r (N/r)
    (fun a => ((k%(r*a) : ℕ) : ℝ)/(r*a : ℕ))
    (fun a => ((k%(r*a) : ℕ) : ℝ)/(r*a : ℕ))

/-- The harmonic coefficient of the physical gcd-r quadratic head. -/
def harmonicQuadratic (r N : ℕ) : ℝ :=
  (mu r)^2/(r : ℝ)^2*pairForm r (N/r) (fun a => 1/a) (fun a => 1/a)

/-- Exact identification with the original Möbius coefficients at the original moduli. -/
theorem residueQuadratic_eq_actual (r N k : ℕ) :
    residueQuadratic r N k = ∑ a ∈ Icc 1 (N/r), ∑ b ∈ Icc 1 (N/r),
      (if a.Coprime b then mu (r*a)*mu (r*b) else 0)*
        (((k%(r*a) : ℕ) : ℝ)/(r*a : ℕ))*(((k%(r*b) : ℕ) : ℝ)/(r*b : ℕ)) := by
  simp only [residueQuadratic, pairForm, Finset.mul_sum, mu_mul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases h : a.Coprime b
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

private def mixedColumn (r Q t : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Q, maskedMu r a/(a : ℝ)*((primeSupportedIcc (r*a) t).card : ℝ)
private def floorColumn (r Q t : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Q, maskedMu r a*(t/a : ℕ)*((primeSupportedIcc (r*a) t).card : ℝ)

private theorem residue_remainder_eq {r N k : ℕ} (hr : 0<r) (hkN : k≤N) :
    residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N =
      (mu r)^2*(-2*((k : ℝ)/r)*mixedColumn r (N/r) (k/r)+floorColumn r (N/r) (k/r)) := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast hr.ne'
  have htQ : k/r≤N/r := Nat.div_le_div_right hkN
  have hmod : ∀ a ∈ Icc 1 (N/r), ((k%(r*a) : ℕ) : ℝ)/(r*a : ℕ) =
      ((k : ℝ)/r)*(1/a)-((k/r)/a : ℕ) := by
    intro a ha
    have ha0 : (a : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp ha).1)
    have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.mod_add_div k (r*a))
    push_cast at he ⊢
    rw [Nat.div_div_eq_div_mul]
    field_simp
    nlinarith
  have hfun : residueQuadratic r N k = (mu r)^2*pairForm r (N/r)
      (fun a => ((k : ℝ)/r)*(1/a)-((k/r)/a : ℕ))
      (fun a => ((k : ℝ)/r)*(1/a)-((k/r)/a : ℕ)) := by
    unfold residueQuadratic pairForm
    congr 1
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    dsimp only
    rw [hmod a ha, hmod b hb]
  have hmix : pairForm r (N/r) (fun a => ((k : ℝ)/r)*(1/a))
      (fun b => ((k/r)/b : ℕ)) = ((k : ℝ)/r)*mixedColumn r (N/r) (k/r) := by
    rw [pairForm_left_scale, pairForm_floor_column htQ]
    congr 1
    apply sum_congr rfl
    intro a _
    ring
  have hfloor : pairForm r (N/r) (fun a => ((k/r)/a : ℕ))
      (fun b => ((k/r)/b : ℕ)) = floorColumn r (N/r) (k/r) :=
    pairForm_floor_column htQ r _
  rw [hfun, pairForm_sub_square, hmix, hfloor, pairForm_left_scale,
    pairForm_symm r (N/r) (fun a => 1/a) (fun a => ((k : ℝ)/r)*(1/a)), pairForm_left_scale]
  unfold harmonicQuadratic
  field_simp
  ring


private theorem exists_numerator_bound {δ : ℝ} (hδ : 0<δ) :
    ∃ C : ℝ, 0<C ∧ ∀ N r k : ℕ, 0<r → 0<k → k≤N →
      |residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N| ≤
        3*C*(N : ℝ)^(2*δ)*(1+Real.log N)*((k : ℝ)/r) := by
  obtain ⟨C,hC,hcount⟩ := exists_supportedCount_le hδ hδ
  refine ⟨C,hC,?_⟩
  intro N r k hr hk hkN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast lt_of_lt_of_le hk hkN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast lt_of_lt_of_le hk hkN
  have hr0 : (0 : ℝ)<r := by exact_mod_cast hr
  have hk0 : (0 : ℝ)<k := by exact_mod_cast hk
  let H : ℝ := 1+Real.log N
  let A : ℝ := C*(N : ℝ)^(2*δ)
  let v : ℝ := (k : ℝ)/r
  have hH : 0≤H := by dsimp [H]; linarith [Real.log_nonneg hN1]
  have hA : 0≤A := by dsimp [A]; positivity
  have hv : 0≤v := by dsimp [v]; positivity
  rw [residue_remainder_eq hr hkN]
  rcases Nat.eq_zero_or_pos (k/r) with hz | ht
  · simp [hz, mixedColumn, floorColumn, primeSupportedIcc]
    positivity
  have hs (a : ℕ) (ha : a∈Icc 1 (N/r)) :
      ((primeSupportedIcc (r*a) (k/r)).card : ℝ)≤A := by
    have ha0 : 0<a := (mem_Icc.mp ha).1
    have hra : r*a≤N := by
      have h := (Nat.le_div_iff_mul_le hr).mp (mem_Icc.mp ha).2
      simpa [Nat.mul_comm] using h
    have htN : k/r≤N := (Nat.div_le_self k r).trans hkN
    have hp : ((r*a : ℕ) : ℝ)^δ≤(N : ℝ)^δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hra) hδ.le
    have htp : ((k/r : ℕ) : ℝ)^δ≤(N : ℝ)^δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast htN) hδ.le
    calc
      _ ≤ C*((k/r : ℕ) : ℝ)^δ*((r*a : ℕ) : ℝ)^δ := hcount (r*a) (k/r) (by positivity) ht
      _ ≤ C*(N : ℝ)^δ*(N : ℝ)^δ :=
        mul_le_mul (mul_le_mul_of_nonneg_left htp hC.le) hp (by positivity) (by positivity)
      _ = A := by dsimp [A]; rw [mul_assoc, ← Real.rpow_add hN0]; congr 2; ring
  have hHsum : (∑ a ∈ Icc 1 (N/r), 1/(a : ℝ))≤H := by
    calc
      _ ≤ ∑ a ∈ Icc 1 N, 1/(a : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Icc_subset_Icc le_rfl (Nat.div_le_self N r)) (fun a _ _ => by positivity)
      _ ≤ H := sum_Icc_one_div_le_one_add_log N
  have hL : |mixedColumn r (N/r) (k/r)|≤A*H := by
    calc
      _ ≤ ∑ a ∈ Icc 1 (N/r),
          |maskedMu r a/(a : ℝ)*((primeSupportedIcc (r*a) (k/r)).card : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Icc 1 (N/r), A*(1/(a : ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha0 : (0 : ℝ)<a := by exact_mod_cast (mem_Icc.mp ha).1
        calc
          _ = (|maskedMu r a|/(a : ℝ))*((primeSupportedIcc (r*a) (k/r)).card : ℝ) := by
            rw [abs_mul, abs_div, abs_of_pos ha0,
              abs_of_nonneg (show (0 : ℝ)≤((primeSupportedIcc (r*a) (k/r)).card : ℝ) by positivity)]
          _ ≤ (1/(a : ℝ))*A := mul_le_mul
            (div_le_div_of_nonneg_right (abs_maskedMu_le r a) ha0.le) (hs a ha)
            (by positivity) (by positivity)
          _ = _ := by ring
      _ = A*(∑ a ∈ Icc 1 (N/r), 1/(a : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ A*H := mul_le_mul_of_nonneg_left hHsum hA
  have hF : |floorColumn r (N/r) (k/r)|≤v*A*H := by
    calc
      _ ≤ ∑ a ∈ Icc 1 (N/r),
          |maskedMu r a*((k/r)/a : ℕ)*((primeSupportedIcc (r*a) (k/r)).card : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Icc 1 (N/r), (v*A)*(1/(a : ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha0 : (0 : ℝ)<a := by exact_mod_cast (mem_Icc.mp ha).1
        have hf : (((k/r)/a : ℕ) : ℝ)≤v/a := by
          calc
            _ ≤ ((k/r : ℕ) : ℝ)/a := Nat.cast_div_le
            _ ≤ v/a := div_le_div_of_nonneg_right Nat.cast_div_le ha0.le
        calc
          _ = |maskedMu r a| *((k/r)/a : ℕ)*((primeSupportedIcc (r*a) (k/r)).card : ℝ) := by
            rw [abs_mul, abs_mul,
              abs_of_nonneg (show (0 : ℝ)≤(((k/r)/a : ℕ) : ℝ) by positivity),
              abs_of_nonneg (show (0 : ℝ)≤((primeSupportedIcc (r*a) (k/r)).card : ℝ) by positivity)]
          _ ≤ 1*(v/a)*A := mul_le_mul
            (mul_le_mul (abs_maskedMu_le r a) hf (by positivity) (by norm_num))
            (hs a ha) (by positivity) (by positivity)
          _ = _ := by ring
      _ = (v*A)*(∑ a ∈ Icc 1 (N/r), 1/(a : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ v*A*H := mul_le_mul_of_nonneg_left hHsum (mul_nonneg hv hA)
  have hm : (mu r)^2≤1 := by
    have h := abs_le.mp (abs_mu_le r)
    nlinarith [sq_nonneg (mu r)]
  have hsum : |-2*v*mixedColumn r (N/r) (k/r)+floorColumn r (N/r) (k/r)|≤3*v*A*H := by
    calc
      _ ≤ |-2*v*mixedColumn r (N/r) (k/r)|+|floorColumn r (N/r) (k/r)| := abs_add_le _ _
      _ = 2*v*|mixedColumn r (N/r) (k/r)|+|floorColumn r (N/r) (k/r)| := by
        rw [show -2*v*mixedColumn r (N/r) (k/r)=-(2*v*mixedColumn r (N/r) (k/r)) by ring,
          abs_neg, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hv)]
      _ ≤ 2*v*(A*H)+v*A*H := add_le_add (mul_le_mul_of_nonneg_left hL (by positivity)) hF
      _ = _ := by ring
  calc
    _ = (mu r)^2*|-2*v*mixedColumn r (N/r) (k/r)+floorColumn r (N/r) (k/r)| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ 1*(3*v*A*H) := mul_le_mul hm hsum (abs_nonneg _) (by norm_num)
    _ = _ := by dsimp [v,A,H]; ring


/-- Actual weighted initial energy of the exact gcd-r group. -/
def initialEnergy (r N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, residueQuadratic r N k/((k : ℝ)*(k+1))

/-- The total absolute remainder of all gcd heads has arbitrarily small power growth.
The exact harmonic coefficients are retained; no harmonic decay or RH input is used. -/
theorem exists_initialEnergy_remainders_subpower {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ,
      (∑ r ∈ Icc 1 N, |initialEnergy r N-
        harmonicQuadratic r N*DeletionCoprimeHead.headMass N|)≤C*(N : ℝ)^ε := by
  let δ : ℝ := ε/5
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨A,hA,hnum⟩ := exists_numerator_bound hδ
  let D : ℝ := 1+1/δ
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨3*A*D^3,by positivity,?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Real.zero_rpow hε.ne']
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  let H : ℝ := 1+Real.log N
  let K : ℝ := 3*A*(N : ℝ)^(2*δ)*H
  have hH : 0≤H := by dsimp [H]; linarith [Real.log_nonneg hN1]
  have hK : 0≤K := by dsimp [K]; positivity
  have hweight (r k : ℕ) (hr : 0<r) (hk : k∈Icc 1 N) :
      |(residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N)/((k : ℝ)*(k+1))|≤
        K*(1/(r : ℝ))*(1/(k : ℝ)) := by
    have hr0 : (0 : ℝ)<r := by exact_mod_cast hr
    have hk0 : (0 : ℝ)<k := by exact_mod_cast (mem_Icc.mp hk).1
    have hn : |residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N|≤K*((k : ℝ)/r) :=
      hnum N r k hr (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    calc
      _ = |residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N|/((k : ℝ)*(k+1)) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ)<(k : ℝ)*(k+1))]
      _ ≤ (K*((k : ℝ)/r))/((k : ℝ)*(k+1)) := div_le_div_of_nonneg_right hn (by positivity)
      _ = (K/r)/(k+1) := by field_simp
      _ ≤ (K/r)/(k : ℝ) := div_le_div_of_nonneg_left (div_nonneg hK hr0.le) hk0 (by linarith)
      _ = _ := by ring
  have hhead (r : ℕ) (hr : r∈Icc 1 N) :
      |initialEnergy r N-harmonicQuadratic r N*DeletionCoprimeHead.headMass N|≤
        (K*(1/(r : ℝ)))*H := by
    have hs : initialEnergy r N-harmonicQuadratic r N*DeletionCoprimeHead.headMass N =
        ∑ k ∈ Icc 1 N,
          (residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N)/((k : ℝ)*(k+1)) := by
      rw [initialEnergy, DeletionCoprimeHead.headMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hk).1)
      field_simp
    rw [hs]
    calc
      _ ≤ ∑ k ∈ Icc 1 N,
          |(residueQuadratic r N k-(k : ℝ)^2*harmonicQuadratic r N)/((k : ℝ)*(k+1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 N, K*(1/(r : ℝ))*(1/(k : ℝ)) :=
        Finset.sum_le_sum (fun k hk => hweight r k (mem_Icc.mp hr).1 hk)
      _ = (K*(1/(r : ℝ)))*(∑ k ∈ Icc 1 N, 1/(k : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (K*(1/(r : ℝ)))*H :=
        mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) (by positivity)
  have htotal : (∑ r ∈ Icc 1 N, |initialEnergy r N-
      harmonicQuadratic r N*DeletionCoprimeHead.headMass N|)≤K*H^2 := by
    calc
      _ ≤ ∑ r ∈ Icc 1 N, (K*(1/(r : ℝ)))*H := Finset.sum_le_sum hhead
      _ = (K*H)*(∑ r ∈ Icc 1 N, 1/(r : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ (K*H)*H := mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) (by positivity)
      _ = _ := by ring
  have hlog : H≤D*(N : ℝ)^δ := by
    have hp := Real.one_le_rpow hN1 hδ.le
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg N) hδ
    dsimp [H,D]
    calc
      _ ≤ (N : ℝ)^δ+(N : ℝ)^δ/δ := add_le_add hp hl
      _ = _ := by ring
  have hpowers : (N : ℝ)^(2*δ)*(N : ℝ)^δ*(N : ℝ)^δ*(N : ℝ)^δ=(N : ℝ)^ε := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    dsimp [δ]
    ring
  calc
    _ ≤ K*H^2 := htotal
    _ = 3*A*(N : ℝ)^(2*δ)*H^3 := by dsimp [K]; ring
    _ ≤ 3*A*(N : ℝ)^(2*δ)*(D*(N : ℝ)^δ)^3 := by gcongr
    _ = (3*A*D^3)*((N : ℝ)^(2*δ)*(N : ℝ)^δ*(N : ℝ)^δ*(N : ℝ)^δ) := by ring
    _ = _ := by rw [hpowers]


/-- Coprime cofactor pairs enumerate exactly the original pairs with prescribed positive gcd. -/
theorem gcd_pairs_eq_image {r : ℕ} (hr : 0<r) (N : ℕ) :
    ((Icc 1 N ×ˢ Icc 1 N).filter (fun de => de.1.gcd de.2=r)) =
      (((Icc 1 (N/r) ×ˢ Icc 1 (N/r)).filter (fun ab => ab.1.Coprime ab.2)).image
        (fun ab => (r*ab.1,r*ab.2))) := by
  classical
  ext de
  rcases de with ⟨d,e⟩
  constructor
  · intro h
    obtain ⟨hmem,hg⟩ := mem_filter.mp h
    obtain ⟨hd,he⟩ := mem_product.mp hmem
    have hrd : r∣d := by rw [← hg]; exact Nat.gcd_dvd_left d e
    have hre : r∣e := by rw [← hg]; exact Nat.gcd_dvd_right d e
    have hd0 : 0<d := (mem_Icc.mp hd).1
    have he0 : 0<e := (mem_Icc.mp he).1
    have hda : d/r∈Icc 1 (N/r) := mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hd0 hrd) hr, Nat.div_le_div_right (mem_Icc.mp hd).2⟩
    have heb : e/r∈Icc 1 (N/r) := mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd he0 hre) hr, Nat.div_le_div_right (mem_Icc.mp he).2⟩
    have hab : (d/r).Coprime (e/r) := by
      simpa [hg] using Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left e hd0)
    exact mem_image.mpr ⟨(d/r,e/r),mem_filter.mpr ⟨mem_product.mpr ⟨hda,heb⟩,hab⟩,
      by simp only [Nat.mul_div_cancel' hrd, Nat.mul_div_cancel' hre]⟩
  · intro h
    obtain ⟨⟨a,b⟩,hab,heq⟩ := mem_image.mp h
    have hd : r*a=d := congrArg Prod.fst heq
    have he : r*b=e := congrArg Prod.snd heq
    subst d e
    obtain ⟨hmem,hcop⟩ := mem_filter.mp hab
    obtain ⟨ha,hb⟩ := mem_product.mp hmem
    have hbound (u : ℕ) (hu : u∈Icc 1 (N/r)) : r*u∈Icc 1 N := by
      refine mem_Icc.mpr ⟨Nat.mul_pos hr (mem_Icc.mp hu).1,?_⟩
      have h := (Nat.le_div_iff_mul_le hr).mp (mem_Icc.mp hu).2
      simpa [Nat.mul_comm] using h
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hbound a ha,hbound b hb⟩,?_⟩
    simp only [Nat.gcd_mul_left, hcop.gcd_eq_one, Nat.mul_one]

/-- The harmonic term retains the original moduli and original Möbius coefficients. -/
theorem harmonicQuadratic_eq_actual {r : ℕ} (hr : 0<r) (N : ℕ) :
    harmonicQuadratic r N = ∑ a ∈ Icc 1 (N/r), ∑ b ∈ Icc 1 (N/r),
      (if a.Coprime b then mu (r*a)*mu (r*b) else 0)/(r*a : ℕ)/(r*b : ℕ) := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast hr.ne'
  simp only [harmonicQuadratic, pairForm, Finset.mul_sum, mu_mul]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  have ha0 : (a : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp ha).1)
  have hb0 : (b : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hb).1)
  by_cases h : a.Coprime b
  · rw [if_pos h, if_pos h]
    push_cast
    field_simp
  · rw [if_neg h, if_neg h]
    simp

/-- Total head variation differs from its full polynomial variation by a subpower amount. -/
theorem exists_initialEnergy_variation_comparison {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ,
      |(∑ r ∈ Icc 1 N, |initialEnergy r N|)-DeletionCoprimeHead.headMass N*
        (∑ r ∈ Icc 1 N, |harmonicQuadratic r N|)|≤C*(N : ℝ)^ε := by
  obtain ⟨C,hC,hrem⟩ := exists_initialEnergy_remainders_subpower hε
  refine ⟨C,hC,?_⟩
  intro N
  have hmass : 0≤DeletionCoprimeHead.headMass N := by
    unfold DeletionCoprimeHead.headMass
    exact sum_nonneg (fun k _ => by positivity)
  have hs : (∑ r ∈ Icc 1 N, |initialEnergy r N|)-DeletionCoprimeHead.headMass N*
      (∑ r ∈ Icc 1 N, |harmonicQuadratic r N|) =
      ∑ r ∈ Icc 1 N, (|initialEnergy r N|-|harmonicQuadratic r N*DeletionCoprimeHead.headMass N|) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro r _
    rw [abs_mul, abs_of_nonneg hmass]
    ring
  rw [hs]
  calc
    _ ≤ ∑ r ∈ Icc 1 N,
        |(|initialEnergy r N|-|harmonicQuadratic r N*DeletionCoprimeHead.headMass N|)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Icc 1 N,
        |initialEnergy r N-harmonicQuadratic r N*DeletionCoprimeHead.headMass N| :=
      Finset.sum_le_sum (fun r _ => abs_abs_sub_abs_le_abs_sub _ _)
    _ ≤ _ := hrem N


/-- Partition the full positive divisor square by its exact gcd. -/
private theorem gcd_pair_partition (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ r ∈ Icc 1 N, ∑ de ∈ (Icc 1 N ×ˢ Icc 1 N).filter
        (fun de => de.1.gcd de.2 = r), F de =
      ∑ de ∈ Icc 1 N ×ˢ Icc 1 N, F de := by
  classical
  calc
    _ = ∑ r ∈ Icc 1 N, ∑ de ∈ Icc 1 N ×ˢ Icc 1 N,
        if de.1.gcd de.2 = r then F de else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_filter]
    _ = ∑ de ∈ Icc 1 N ×ˢ Icc 1 N, ∑ r ∈ Icc 1 N,
        if de.1.gcd de.2 = r then F de else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      rintro ⟨d,e⟩ hde
      have hd : d ∈ Icc 1 N := (mem_product.mp hde).1
      have he : e ∈ Icc 1 N := (mem_product.mp hde).2
      have hgcd : d.gcd e ∈ Icc 1 N := by
        exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left e (mem_Icc.mp hd).1,
          le_trans (Nat.gcd_le_left e (mem_Icc.mp hd).1) (mem_Icc.mp hd).2⟩
      simp [hgcd]

/-- Reassemble every coprime-cofactor gcd group into the literal divisor square. -/
private theorem gcd_group_reassembly (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ r ∈ Icc 1 N, ∑ a ∈ Icc 1 (N/r), ∑ b ∈ Icc 1 (N/r),
      (if a.Coprime b then F (r*a,r*b) else 0) =
    ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, F (d,e) := by
  classical
  have hgroup (r : ℕ) (hr : r ∈ Icc 1 N) :
      ∑ a ∈ Icc 1 (N/r), ∑ b ∈ Icc 1 (N/r),
        (if a.Coprime b then F (r*a,r*b) else 0) =
      ∑ de ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun de => de.1.gcd de.2 = r), F de := by
    rw [gcd_pairs_eq_image (mem_Icc.mp hr).1 N,
      Finset.sum_image (fun x _ y _ hxy => by
        rcases x with ⟨a,b⟩
        rcases y with ⟨c,d⟩
        apply Prod.ext
        · exact Nat.mul_left_cancel (mem_Icc.mp hr).1 (congrArg Prod.fst hxy)
        · exact Nat.mul_left_cancel (mem_Icc.mp hr).1 (congrArg Prod.snd hxy))]
    simp only [Finset.sum_filter, Finset.sum_product]
  calc
    _ = ∑ r ∈ Icc 1 N, ∑ de ∈ (Icc 1 N ×ˢ Icc 1 N).filter
        (fun de => de.1.gcd de.2 = r), F de := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hgroup r hr
    _ = ∑ de ∈ Icc 1 N ×ˢ Icc 1 N, F de := gcd_pair_partition N F
    _ = _ := by rw [Finset.sum_product]

private theorem square_sum (N : ℕ) (q : ℕ → ℝ) :
    ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, q d*q e =
      (∑ d ∈ Icc 1 N, q d)^2 := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]

/-- All exact gcd residue quadratics assemble to the literal modular Möbius square. -/
theorem total_residueQuadratic_eq_bdMobiusModularApproximant_sq (N k : ℕ) :
    ∑ r ∈ Icc 1 N, residueQuadratic r N k =
      bdMobiusModularApproximant N k ^ 2 := by
  calc
    _ = ∑ r ∈ Icc 1 N, ∑ a ∈ Icc 1 (N/r), ∑ b ∈ Icc 1 (N/r),
        if a.Coprime b then
          (mu (r*a)*(((k%(r*a) : ℕ) : ℝ)/(r*a : ℕ))) *
            (mu (r*b)*(((k%(r*b) : ℕ) : ℝ)/(r*b : ℕ)))
        else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [residueQuadratic_eq_actual]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N,
        (mu d * (((k % d : ℕ) : ℝ) / (d : ℝ))) *
          (mu e * (((k % e : ℕ) : ℝ) / (e : ℝ))) :=
      gcd_group_reassembly N (fun de =>
        (mu de.1 * (((k % de.1 : ℕ) : ℝ) / (de.1 : ℝ))) *
          (mu de.2 * (((k % de.2 : ℕ) : ℝ) / (de.2 : ℝ))))
    _ = (∑ d ∈ Icc 1 N,
        mu d * (((k % d : ℕ) : ℝ) / (d : ℝ))) ^ 2 :=
      square_sum N (fun d => mu d * (((k % d : ℕ) : ℝ) / (d : ℝ)))
    _ = _ := by
      unfold bdMobiusModularApproximant
      simp only [mu]
      ring


/-- The total physical initial head is exactly the literal modular Möbius head. -/
theorem total_initialEnergy_eq_bdMobiusModularHead (N : ℕ) :
    ∑ r ∈ Icc 1 N, initialEnergy r N =
      ∑ k ∈ Icc 1 N, bdMobiusModularApproximant N k ^ 2 /
        ((k : ℝ) * (k + 1)) := by
  unfold initialEnergy
  calc
    _ = ∑ k ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
        residueQuadratic r N k / ((k : ℝ) * (k + 1)) := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Icc 1 N,
        (∑ r ∈ Icc 1 N, residueQuadratic r N k) /
          ((k : ℝ) * (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [total_residueQuadratic_eq_bdMobiusModularApproximant_sq]
/-- All exact gcd harmonic coefficients assemble to the physical harmonic Möbius square. -/
theorem total_harmonicQuadratic_eq_deningerHarmonicPartial_sq (N : ℕ) :
    ∑ r ∈ Icc 1 N, harmonicQuadratic r N = deningerHarmonicPartial N ^ 2 := by
  calc
    _ = ∑ r ∈ Icc 1 N, ∑ a ∈ Icc 1 (N/r), ∑ b ∈ Icc 1 (N/r),
        if a.Coprime b then
          (mu (r*a)/(r*a : ℕ))*(mu (r*b)/(r*b : ℕ))
        else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [harmonicQuadratic_eq_actual (mem_Icc.mp hr).1 N]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N,
        (mu d/(d : ℕ))*(mu e/(e : ℕ)) :=
      gcd_group_reassembly N (fun de =>
        (mu de.1/(de.1 : ℕ))*(mu de.2/(de.2 : ℕ)))
    _ = (∑ d ∈ Icc 1 N, mu d/(d : ℕ))^2 :=
      square_sum N (fun d => mu d/(d : ℕ))
    _ = _ := by
      rw [deningerHarmonicPartial_eq_sum_Icc]
      simp only [mu]

/-- The full physical initial head differs from its literal harmonic Möbius square by subpower growth. -/
theorem exists_total_initialEnergy_harmonic_remainder_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |(∑ r ∈ Icc 1 N, initialEnergy r N) -
        DeletionCoprimeHead.headMass N * deningerHarmonicPartial N ^ 2| ≤
        C * (N : ℝ)^ε := by
  obtain ⟨C,hC,hrem⟩ := exists_initialEnergy_remainders_subpower hε
  refine ⟨C,hC,?_⟩
  intro N
  have hsum : (∑ r ∈ Icc 1 N, initialEnergy r N) -
      DeletionCoprimeHead.headMass N * deningerHarmonicPartial N ^ 2 =
      ∑ r ∈ Icc 1 N,
        (initialEnergy r N-harmonicQuadratic r N*DeletionCoprimeHead.headMass N) := by
    rw [← total_harmonicQuadratic_eq_deningerHarmonicPartial_sq]
    calc
      _ = (∑ r ∈ Icc 1 N, initialEnergy r N) -
          ∑ r ∈ Icc 1 N, harmonicQuadratic r N*DeletionCoprimeHead.headMass N := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hsum]
  calc
    _ ≤ ∑ r ∈ Icc 1 N,
        |initialEnergy r N-harmonicQuadratic r N*DeletionCoprimeHead.headMass N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := hrem N

/-- The exact initial gcd head is bounded by the complete literal primitive energy.  Every
complementary coordinate of that energy remains present on the right. -/
theorem total_initialEnergy_le_primitiveEnergy (N : ℕ) :
    (∑ r ∈ Icc 1 N, initialEnergy r N) ≤ DeletionMobiusPrimitive.primitiveEnergy N := by
  rw [total_initialEnergy_eq_bdMobiusModularHead]
  have hhead :
      (∑ k ∈ Icc 1 N, bdMobiusModularApproximant N k ^ 2 /
        ((k : ℝ) * (k + 1))) =
      ∑ n ∈ Finset.range N, bdMobiusModularApproximant N (n + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      push_cast
      ring
  have hterm (n : ℕ) :
      bdMobiusModularApproximant N (n + 1) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤
        DeletionMobiusPrimitive.normalizedPrimitive N n ^ 2 := by
    rw [DeletionMobiusPrimitive.normalizedPrimitive,
      DeletionMobiusPrimitive.primitive_eq_modular, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (bdMobiusModularApproximant N (n + 1))]
  rw [hhead]
  calc
    _ ≤ ∑ n ∈ Finset.range N, DeletionMobiusPrimitive.normalizedPrimitive N n ^ 2 :=
      Finset.sum_le_sum fun n _ => hterm n
    _ ≤ ∑' n : ℕ, DeletionMobiusPrimitive.normalizedPrimitive N n ^ 2 :=
      (DeletionMobiusPrimitive.summable_normalizedPrimitive_sq N).sum_le_tsum
        (Finset.range N) fun n _ => sq_nonneg _
    _ = _ := rfl

/-- The deterministic mass of the first `N` critical carrier coordinates is at least `N/2`. -/
theorem half_nat_le_headMass (N : ℕ) :
    (N : ℝ) / 2 ≤ DeletionCoprimeHead.headMass N := by
  calc
    (N : ℝ) / 2 = ∑ k ∈ Icc 1 N, (1 : ℝ) / 2 := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ ∑ k ∈ Icc 1 N, (k : ℝ) / (k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      nlinarith
    _ = _ := rfl

/-- Any cofinal subpower ceiling for the complete EDQ primitive energy must suppress the
literal harmonic Möbius scalar at its square-root scale.  The subpower remainder is exact;
the missing ingredient is an upper law for the primitive energy itself. -/
theorem exists_harmonic_head_le_primitiveEnergy_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (N : ℝ) / 2 * deningerHarmonicPartial N ^ 2 ≤
        DeletionMobiusPrimitive.primitiveEnergy N + C * (N : ℝ) ^ ε := by
  obtain ⟨C, hC, hrem⟩ := exists_total_initialEnergy_harmonic_remainder_subpower hε
  refine ⟨C, hC, ?_⟩
  intro N
  have hhead := total_initialEnergy_le_primitiveEnergy N
  have hmean : DeletionCoprimeHead.headMass N * deningerHarmonicPartial N ^ 2 ≤
      (∑ r ∈ Icc 1 N, initialEnergy r N) + C * (N : ℝ) ^ ε := by
    have habs := (abs_le.mp (hrem N)).1
    linarith
  calc
    (N : ℝ) / 2 * deningerHarmonicPartial N ^ 2 ≤
        DeletionCoprimeHead.headMass N * deningerHarmonicPartial N ^ 2 :=
      mul_le_mul_of_nonneg_right (half_nat_le_headMass N) (sq_nonneg _)
    _ ≤ (∑ r ∈ Icc 1 N, initialEnergy r N) + C * (N : ℝ) ^ ε := hmean
    _ ≤ _ := add_le_add_right hhead _

end RHTower.DeletionGcdHead
