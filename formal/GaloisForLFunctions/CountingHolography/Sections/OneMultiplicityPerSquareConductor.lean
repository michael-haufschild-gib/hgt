import GaloisForLFunctions.CountingHolography.Sections.UniformQuadratureForPrimeContacts
import GaloisForLFunctions.CountingHolography.Sections.DoublingOnThreeFixedMultiplicities
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# One multiplicity per square conductor

On a signed spline ray the ordinary prime product approaches the continuous
contact sum. Floor errors cost the Chebyshev mass of the entire window.
The mesh errors cost only its square root divided by the resolution.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction AbsoluteGeometryOfSpecZ
open ArithmeticScatteringHolography SquareRootThreshold

/-- Ordinary prime degrees in the finite contact window. -/
def ordinaryPrimeLags (L : ℕ) := (Icc 2 L).filter Nat.Prime

/-- The continuous ordinary-prime contact sum of the integer spline. -/
def ordinaryPrimeContact {N : ℕ} (a : Fin N → ℤ) :=
  ∑ k ∈ ordinaryPrimeLags (3*windowEnd N), integratedContact a k*vonMangoldt k

/-- The two log-weight bounds for floor loss and harmonic quadrature. -/
theorem ordinaryPrimeLagSums (L : ℕ) :
    (∑ k ∈ ordinaryPrimeLags L, vonMangoldt k) ≤ 7*L ∧
    (∑ k ∈ ordinaryPrimeLags L, vonMangoldt k/Real.sqrt k) ≤ 34*Real.sqrt L := by
  have hs {k : ℕ} (hk : k ∈ ordinaryPrimeLags L) : 2 ≤ k ∧ k ≤ L := mem_Icc.mp (mem_filter.mp hk).1
  constructor
  · refine (sum_le_sum_of_subset_of_nonneg (s := ordinaryPrimeLags L) (t := Icc 1 L) (fun k hk =>
      mem_Icc.mpr ⟨Nat.le_trans (by decide : 1 ≤ 2) (hs hk).1,(hs hk).2⟩)
      (fun _ _ _ => vonMangoldt_nonneg)).trans (_root_.RHTower.sum_vonMangoldt_Icc_le_seven L)
  · refine (sum_le_sum_of_subset_of_nonneg (s := ordinaryPrimeLags L) (t := Ioc 0 L) (fun k hk =>
      mem_Ioc.mpr ⟨Nat.lt_of_lt_of_le (by decide : 0 < 2) (hs hk).1,(hs hk).2⟩)
      (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))).trans
      (_root_.RHTower.sum_vonMangoldt_div_sqrt_le L)

/-- The total log weight lost when the real contact rows are rounded down. -/
def ordinaryFloorLoss {N : ℕ} (a : Fin N → ℤ) :=
  let L := 3*windowEnd N
  ∑ k ∈ ordinaryPrimeLags L,
    Int.fract (contactMultiplicity (packet a) L (resolution a) k)*vonMangoldt k

theorem ordinaryFloorLoss_bounds {N : ℕ} (a : Fin N → ℤ) :
    0 ≤ ordinaryFloorLoss a ∧ ordinaryFloorLoss a ≤ 7*(3*windowEnd N : ℕ) := by
  refine ⟨sum_nonneg fun _ _ => mul_nonneg (Int.fract_nonneg _) vonMangoldt_nonneg,?_⟩
  exact (sum_le_sum fun k _ => mul_le_of_le_one_left vonMangoldt_nonneg
    (Int.fract_lt_one (contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k)).le).trans
    (ordinaryPrimeLagSums _).1

/-- Adding the exact floor loss leaves only the uniform quadrature error.
The bound has square-root dependence on the length of the prime window. -/
theorem ordinaryPrimeContact_sampling_at_mass {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    (∑ i, |(a i : ℝ)|) ≤ M → ∀ m : ℕ, 0 < resolution (m • a) →
      let L := 3*windowEnd N
      |Real.log (ordinaryPrimeGenerator (m • a) : ℝ)+ordinaryFloorLoss (m • a)-
        (m:ℝ)^2*ordinaryPrimeContact a| ≤ ((m:ℝ)^2*C/resolution (m • a))*Real.sqrt L := by
  obtain ⟨C,hC,h⟩ := contactMultiplicity_error_at_mass hM
  refine ⟨68*C,by positivity,fun N a ha m hr => ?_⟩
  let r := resolution (m • a)
  let L := 3*windowEnd N
  let t := (m:ℝ)^2
  let D := t*2*C/r
  let x := fun k => contactMultiplicity (packet (m • a)) L r k
  have hD : 0 ≤ D := by unfold D t; positivity
  have hrow (k : ℕ) (hk : k ∈ ordinaryPrimeLags L) :
      |x k-t*integratedContact a k| ≤ D/Real.sqrt k := by
    have hq := h N a ha hr (mem_filter.mp hk).2.pos
    have he : x k = t*contactMultiplicity (packet a) L r k := by
      unfold x
      rw [packet_smul,contactMultiplicity_scale]
    rw [he,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg (m:ℝ))]
    refine (mul_le_mul_of_nonneg_left hq (sq_nonneg _)).trans (le_of_eq ?_)
    unfold D
    ring
  have he : Real.log (ordinaryPrimeGenerator (m • a) : ℝ)+ordinaryFloorLoss (m • a) =
      ∑ k ∈ ordinaryPrimeLags L, x k*vonMangoldt k := by
    rw [log_ordinaryPrimeGenerator]
    change (∑ k ∈ ordinaryPrimeLags L, (⌊x k⌋ : ℝ)*vonMangoldt k) +
      (∑ k ∈ ordinaryPrimeLags L, Int.fract (x k)*vonMangoldt k) = _
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← add_mul,Int.floor_add_fract]
  rw [he]
  change |(∑ k ∈ ordinaryPrimeLags L, x k*vonMangoldt k) -
    t*(∑ k ∈ ordinaryPrimeLags L, integratedContact a k*vonMangoldt k)| ≤ _
  rw [mul_sum,← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ ordinaryPrimeLags L, D*(vonMangoldt k/Real.sqrt k) := by
          refine sum_le_sum fun k hk => ?_
          rw [← mul_assoc,← sub_mul,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
          exact (mul_le_mul_of_nonneg_right (hrow k hk) vonMangoldt_nonneg).trans_eq (by ring)
    _ ≤ D*(34*Real.sqrt L) := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (ordinaryPrimeLagSums L).2 hD
    _ = _ := by dsimp only [D,t,r,L]; ring

/-- Sampling on a horizon of arbitrary length at total variation four. -/
theorem ordinaryPrimeContact_sampling_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    (∑ i, |(a i : ℝ)|) ≤ 4 → ∀ m : ℕ, 0 < resolution (m • a) →
      let L := 3*windowEnd N
      |Real.log (ordinaryPrimeGenerator (m • a) : ℝ)+ordinaryFloorLoss (m • a)-
        (m:ℝ)^2*ordinaryPrimeContact a| ≤ ((m:ℝ)^2*C/resolution (m • a))*Real.sqrt L :=
  ordinaryPrimeContact_sampling_at_mass (by norm_num)

/-- The two errors in an ordinary prime product, with their dependence
on the window length and the actual mesh resolution. -/
theorem ordinaryPrimeContact_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    (∑ i, |(a i : ℝ)|) ≤ 4 → ∀ m : ℕ, 0 < resolution (m • a) →
      let L := 3*windowEnd N
      |Real.log (ordinaryPrimeGenerator (m • a) : ℝ)-(m:ℝ)^2*ordinaryPrimeContact a| ≤
        7*L + ((m:ℝ)^2*C/resolution (m • a))*Real.sqrt L := by
  obtain ⟨C,hC,h⟩ := ordinaryPrimeContact_sampling_error
  refine ⟨C,hC,fun N a ha m hr => ?_⟩
  obtain ⟨hlo,hhi⟩ := abs_le.mp (h N a ha m hr)
  obtain ⟨hf,hf'⟩ := ordinaryFloorLoss_bounds (m • a)
  dsimp only
  rw [abs_le]
  constructor <;> linarith only [hlo,hhi,hf,hf',Nat.cast_nonneg (α := ℝ) (3*windowEnd N)]

/-- The prime horizon on the three squares grows at most quadratically. -/
theorem successorSquare_window_bound : ∃ A : ℝ, 1 ≤ A ∧ ∀ {n : ℕ}, 0 < n →
    ((3*windowEnd ((2*n+1)^2+1) : ℕ):ℝ) ≤ (A*n)^2 := by
  let E := Real.exp (Real.log 3+10)
  let A := 33*E+3
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hA : 1 ≤ A := by unfold A; linarith only [hE]
  refine ⟨A,hA,fun {n} hn => ?_⟩
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hb : (2*(n:ℝ)+1)^2 ≤ (3*(n:ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hn1]) 2
  let N := (2*n+1)^2+1
  have hN : (N:ℝ)+1 ≤ 11*(n:ℝ)^2 := by
    unfold N
    push_cast
    linarith only [hb,one_le_pow₀ hn1 (n := 2)]
  have hw : (windowEnd N : ℝ) ≤ E*((N:ℝ)+1)+1 := by
    change (⌈Real.exp ((Real.log 3+5)+Real.log ((N:ℝ)+1)+5)⌉₊ : ℝ) ≤ _
    rw [show (Real.log 3+5)+Real.log ((N:ℝ)+1)+5 = (Real.log 3+10)+Real.log ((N:ℝ)+1) by ring,
      Real.exp_add,Real.exp_log (by positivity)]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  change ((3*windowEnd N : ℕ):ℝ) ≤ _
  push_cast
  calc _ ≤ A*(n:ℝ)^2 := by
        unfold A
        linarith only [hw,mul_le_mul_of_nonneg_left hN hE,one_le_pow₀ hn1 (n := 2)]
    _ ≤ _ := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hA (by decide : 2 ≠ 0)) (sq_nonneg _)

/-- Rounding costs at most a constant times n² and sampling costs at most
a constant times n m, simultaneously at every positive multiplicity. -/
theorem successorSquare_contact_error_all : ∃ D : ℝ, 0 ≤ D ∧ ∀ {n m : ℕ}, 0 < n → 0 < m →
    |Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ) -
      (m:ℝ)^2*ordinaryPrimeContact (successorSquareTriple n)| ≤ D*((n:ℝ)^2+n*m) := by
  obtain ⟨A,hA,hL⟩ := successorSquare_window_bound
  obtain ⟨C,hC,hc⟩ := ordinaryPrimeContact_error
  have hA' := zero_le_one.trans hA
  refine ⟨7*A^2+C*A,by positivity,fun {n m} hn hm => ?_⟩
  let L := 3*windowEnd ((2*n+1)^2+1)
  let r := resolution (m • successorSquareTriple n)
  have hr : m ≤ r := successorSquare_resolution_ge n m
  have hr' : (m : ℝ) ≤ r := by exact_mod_cast hr
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hn' := (Nat.cast_pos.mpr hn : (0:ℝ) < n)
  have hl : (L:ℝ) ≤ (A*n)^2 := hL hn
  have hroot := Real.sqrt_le_sqrt hl
  rw [Real.sqrt_sq (mul_nonneg hA' hn'.le)] at hroot
  have hdiv : (m:ℝ)^2*C/r ≤ (m:ℝ)*C := by
    apply (div_le_iff₀ (hm'.trans_le hr')).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hr' (mul_nonneg hm'.le hC)]
  have he := hc _ _ (successorSquareTriple_mass n) m (hm.trans_le hr)
  refine he.trans ?_
  change 7*(L:ℝ)+((m:ℝ)^2*C/r)*Real.sqrt L ≤ _
  have h₂ := mul_le_mul hdiv hroot (Real.sqrt_nonneg _) (mul_nonneg hm'.le hC)
  linarith only [hl,h₂,mul_nonneg (mul_nonneg hC hA') (sq_nonneg (n:ℝ)),
    mul_nonneg (sq_nonneg A) (mul_nonneg hn'.le hm'.le)]

/-- Beyond the conductor parameter the normalized ordinary-prime logarithm
has bounded error with one constant for all conductors and multiplicities. -/
theorem successorSquare_contact_error : ∃ D : ℝ, 0 ≤ D ∧ ∀ {n m : ℕ}, 0 < n → n ≤ m →
    |Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ) -
      (m:ℝ)^2*ordinaryPrimeContact (successorSquareTriple n)| ≤ D*(m:ℝ)^2 := by
  obtain ⟨D,hD,h⟩ := successorSquare_contact_error_all
  refine ⟨2*D,by positivity,fun {n m} hn hnm => (h hn (hn.trans_le hnm)).trans ?_⟩
  have he : (n:ℝ) ≤ m := by exact_mod_cast hnm
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) he 2
  have hprod := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) m)
  have hsum : (n:ℝ)^2+n*m ≤ 2*(m:ℝ)^2 := by linarith only [hsq,hprod]
  exact (mul_le_mul_of_nonneg_left hsum hD).trans_eq (by ring)

/-- Integrating only the ordinary prime rows recovers the negative Weil
degree to bounded error, uniformly in the three square conductors. -/
theorem successorSquare_contact_degree : ∃ A : ℝ, 0 ≤ A ∧ ∀ {n : ℕ}, 0 < n →
    |ordinaryPrimeContact (successorSquareTriple n)+integerProbe _ (successorSquareTriple n)| ≤ A := by
  obtain ⟨D,hD,hd⟩ := successorSquare_contact_error
  obtain ⟨C,hC,hc⟩ := poleBalanced_ordinary_error
  refine ⟨D+16*C+4,by positivity,fun {n} hn => ?_⟩
  let a := successorSquareTriple n
  obtain ⟨m,he,hm⟩ := ((hc _ a (positivePoleDegree_successorSquareTriple hn)).and (eventually_ge_atTop n)).exists
  have ht : 0 < (m:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (hn.trans_le hm))
  have hmass := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2) hC
  have h₁ := hd hn hm
  have h₂ : C*(∑ i, |(a i : ℝ)|)^2+4 ≤ 16*C+4 := by linarith only [hmass]
  have h₃ := he.trans (mul_le_mul_of_nonneg_right h₂ ht.le)
  obtain ⟨hlo,hhi⟩ := abs_le.mp h₁
  obtain ⟨hlo',hhi'⟩ := abs_le.mp h₃
  rw [abs_le]
  constructor <;> apply (mul_le_mul_iff_right₀ ht).mp <;>
    linarith only [hlo,hhi,hlo',hhi']

/-- After division by the square-root conductor, the signed prime contact
tends to zero through every integer conductor. -/
theorem successorSquare_contact_sublinear :
    Tendsto (fun n : ℕ => ordinaryPrimeContact (successorSquareTriple n)/((n:ℝ)+1)) atTop (𝓝 0) := by
  let X := fun n : ℕ => (n:ℝ)+1
  let P := fun n => ordinaryPrimeContact (successorSquareTriple n)
  let Q := fun n => integerProbe _ (successorSquareTriple n)
  obtain ⟨D,_,h⟩ := successorSquare_contact_degree
  have hX : Tendsto X atTop atTop := tendsto_atTop_mono
    (f := fun n : ℕ => (n:ℝ)) (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n => (P n+Q n)/X n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => D/X n) _ (tendsto_const_nhds.div_atTop hX)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (show 0 ≤ X n by unfold X; positivity)]
    exact div_le_div_of_nonneg_right (h hn) (by unfold X; positivity)
  have hq : Tendsto (fun n => Q n/X n) atTop (𝓝 0) := successorSquare_degree_sublinear
  simpa only [add_div,add_sub_cancel_right,sub_zero,P,X] using he.sub hq

/-- The signed logarithm is uniformly negligible relative to n m²
as the squared multiplicity grows compared with n. -/
theorem successorSquare_log_negligible {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, K*n ≤ (m:ℝ)^2 →
      |Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ)| ≤ ε*n*(m:ℝ)^2 := by
  obtain ⟨D,hD,h⟩ := successorSquare_contact_error_all
  let K := max 1 (4*D/ε)
  have hK : 1 ≤ K := le_max_left _ _
  have hDK : 4*D ≤ K*ε := (div_le_iff₀ hε).mp (le_max_right _ _)
  have hnear := successorSquare_contact_sublinear.abs.eventually_le_const (show |(0:ℝ)| < ε/4 by
    rw [abs_zero]; positivity)
  refine ⟨K,hK,?_⟩
  filter_upwards [hnear,eventually_ge_atTop ⌈K^2⌉₊,eventually_ge_atTop 1] with n hp hnK hn
  intro m hmn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 := zero_le_one.trans hn'
  have hK2 : K^2 ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnK)
  have hn2 := (le_mul_of_one_le_left hn0 hK).trans hmn
  have hKm := le_of_pow_le_pow_left₀ two_ne_zero (Nat.cast_nonneg (α := ℝ) m) (hK2.trans hn2)
  have hm : 0 < m := by exact_mod_cast zero_lt_one.trans_le (hK.trans hKm)
  let P := ordinaryPrimeContact (successorSquareTriple n)
  let t := (m:ℝ)^2
  let z := Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ)
  have ht : 0 ≤ t := sq_nonneg _
  change |P/((n:ℝ)+1)| ≤ ε/4 at hp
  have hx : 0 < (n:ℝ)+1 := by positivity
  rw [abs_div,abs_of_pos hx] at hp
  have hp' : |P| ≤ ε/2*n := by
    linarith only [(div_le_iff₀ hx).mp hp,
      mul_le_mul_of_nonneg_left hn' hε.le]
  have h₁ : 4*D*n ≤ ε*t := calc
    _ ≤ (K*ε)*n := mul_le_mul_of_nonneg_right hDK hn0
    _ = ε*(K*n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmn hε.le
  have h₂ : 4*D ≤ ε*m := hDK.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hKm hε.le)
  have herr : |z-t*P| ≤ D*((n:ℝ)^2+n*m) := h hn hm
  have hab := abs_add_le (z-t*P) (t*P)
  rw [sub_add_cancel,abs_mul,abs_of_nonneg ht] at hab
  have h₂' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (α := ℝ) m)) hn0
  dsimp only [t] at *
  linarith only [hab,herr,mul_le_mul_of_nonneg_right h₁ hn0,h₂',mul_le_mul_of_nonneg_left hp' ht]

/-- On the conductor window the logarithmic generator plus the scaled
degree has a uniform quadratic error. -/
theorem successorSquare_degree_window_error : ∃ E : ℝ, 0 ≤ E ∧ ∀ {n m : ℕ}, 0 < n → 0 < m →
    (m:ℝ) ≤ 2*((n:ℝ)+1) →
    |Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ) +
      (m:ℝ)^2*integerProbe _ (successorSquareTriple n)| ≤ E*((n:ℝ)+1)^2 := by
  obtain ⟨C,hC,h⟩ := successorSquare_contact_error_all
  obtain ⟨D,hD,hd⟩ := successorSquare_contact_degree
  refine ⟨3*C+4*D,by positivity,fun {n m} hn hm hmn => ?_⟩
  let a := successorSquareTriple n
  let P := ordinaryPrimeContact a
  let Q := integerProbe _ a
  let t := (m:ℝ)^2
  let x := Real.log (ordinaryPrimeGenerator (m • a) : ℝ)
  have herr : |x-t*P| ≤ C*((n:ℝ)^2+n*m) := h hn hm
  have hdeg : |P+Q| ≤ D := hd hn
  have h₁ : (n:ℝ)^2+n*m ≤ 3*((n:ℝ)+1)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hmn (Nat.cast_nonneg (α := ℝ) n),Nat.cast_nonneg (α := ℝ) n]
  have h₂ : t ≤ 4*((n:ℝ)+1)^2 := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hmn 2
    change (m:ℝ)^2 ≤ _
    linarith only [hsq]
  change |x+t*Q| ≤ _
  rw [show x+t*Q = (x-t*P)+t*(P+Q) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_of_nonneg (sq_nonneg (m:ℝ))]
  linarith only [herr,mul_le_mul_of_nonneg_left h₁ hC,
    mul_le_mul_of_nonneg_left hdeg (sq_nonneg (m:ℝ)),mul_le_mul_of_nonneg_right h₂ hD]

private theorem logPower {N : ℕ} (a : Fin N → ℤ) {B : ℕ} (hB : 0 < B) (m : ℕ) :
    ordinaryPrimeGenerator a ≤ (B:ℚ)^(m^2) ↔
      Real.log (ordinaryPrimeGenerator a : ℝ) ≤ Real.log B*(m:ℝ)^2 := by
  simpa only [one_mul,Nat.cast_one,one_pow,mul_one] using generator_le_power_iff a hB 1 m

/-- One prescribed multiplicity at each square conductor suffices. The
bound compares two rationals and has a common integer base. -/
theorem riemannHypothesis_iff_chosen_successorSquare_power (μ : ℕ → ℕ) (hμ : ∀ n, n ≤ μ n) :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      ordinaryPrimeGenerator (μ n • successorSquareTriple n) ≤ (B:ℚ)^((μ n)^2) := by
  obtain ⟨D,_,hd⟩ := successorSquare_contact_error
  have transfer {n m k B : ℕ} (hn : 0 < n) (hm : n ≤ m) (hk : n ≤ k) (hb : 0 < B)
      (hf : ordinaryPrimeGenerator (m • successorSquareTriple n) ≤ (B:ℚ)^(m^2)) :
      Real.log (ordinaryPrimeGenerator (k • successorSquareTriple n) : ℝ) ≤
        (Real.log B+2*D)*(k:ℝ)^2 := by
    have h₁ := (logPower _ hb m).mp hf
    have hp : ordinaryPrimeContact (successorSquareTriple n) ≤ Real.log B+D := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (Nat.cast_pos.mpr (hn.trans_le hm) : 0<(m:ℝ)))).mp
      linarith only [h₁,(abs_le.mp (hd hn hm)).1]
    have h₂ := mul_le_mul_of_nonneg_right hp (sq_nonneg (k:ℝ))
    linarith only [h₂,(abs_le.mp (hd hn hk)).2]
  have base (B : ℕ) : ∃ H : ℕ, 0 < H ∧ Real.log B+2*D ≤ Real.log H := by
    refine ⟨⌈Real.exp (Real.log B+2*D)⌉₊,Nat.ceil_pos.mpr (Real.exp_pos _),?_⟩
    exact (Real.le_log_iff_exp_le (Nat.cast_pos.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)))).mpr (Nat.le_ceil _)
  rw [riemannHypothesis_iff_successorSquare_power]
  constructor
  · rintro ⟨B,hB,h⟩
    obtain ⟨H,hH,hbase⟩ := base B
    refine ⟨H,hH,fun n hn => (logPower _ hH _).mpr ?_⟩
    obtain ⟨m,hfit,hm⟩ := ((h n hn).and_eventually (eventually_ge_atTop n)).exists
    exact (transfer hn hm (hμ n) hB hfit).trans (mul_le_mul_of_nonneg_right hbase (sq_nonneg _))
  · rintro ⟨B,hB,h⟩
    obtain ⟨H,hH,hbase⟩ := base B
    refine ⟨H,hH,fun n hn => Eventually.frequently ?_⟩
    filter_upwards [eventually_ge_atTop n] with k hk
    exact (logPower _ hH k).mpr ((transfer hn (hμ n) hk hB (h n hn)).trans
      (mul_le_mul_of_nonneg_right hbase (sq_nonneg _)))

/-- The ordinary prime product at multiplicity exactly n detects RH. -/
theorem riemannHypothesis_iff_diagonal_successorSquare_power :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      ordinaryPrimeGenerator (n • successorSquareTriple n) ≤ (B:ℚ)^(n^2) :=
  riemannHypothesis_iff_chosen_successorSquare_power id (fun _ => le_rfl)

/-- Multiplicity at which the fixed comparison exponent (n+1)²
resolves a strip of width s. -/
def stripMultiplicity (s : ℝ) (n : ℕ) := ⌈((n:ℝ)+1)^(1-s)⌉₊

private theorem stripMultiplicity_bounds {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) (n : ℕ) :
    let m := stripMultiplicity s n
    0 < m ∧ (m:ℝ) ≤ 2*((n:ℝ)+1) ∧
    ((n:ℝ)+1)^2 ≤ (m:ℝ)^2*((n:ℝ)+1)^(2*s) ∧
    (m:ℝ)^2*((n:ℝ)+1)^(2*s) ≤ 4*((n:ℝ)+1)^2 := by
  let X := (n:ℝ)+1
  let f := X^(1-s)
  let g := X^s
  let m := stripMultiplicity s n
  have hX : 1 ≤ X := by dsimp only [X]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hx := zero_lt_one.trans_le hX
  have hf : 1 ≤ f := Real.one_le_rpow hX (by linarith only [hs'])
  have hg : 1 ≤ g := Real.one_le_rpow hX hs
  have hfg : f*g = X := by
    unfold f g
    rw [← Real.rpow_add hx,sub_add_cancel,Real.rpow_one]
  have h₁ : f ≤ (m:ℝ) := Nat.le_ceil _
  have h₂ : (m:ℝ) ≤ 2*f := by
    have hh : (m:ℝ) < f+1 := Nat.ceil_lt_add_one (zero_le_one.trans hf)
    linarith only [hh,hf]
  have h₃ : X ≤ (m:ℝ)*g := hfg.symm.le.trans (mul_le_mul_of_nonneg_right h₁ (zero_le_one.trans hg))
  have h₄ : (m:ℝ)*g ≤ 2*X := by
    rw [← hfg,← mul_assoc]
    exact mul_le_mul_of_nonneg_right h₂ (zero_le_one.trans hg)
  have hw : X^(2*s) = g^2 := by
    unfold g
    rw [show 2*s=s*2 by ring,Real.rpow_mul hx.le,Real.rpow_two]
  change 0 < m ∧ (m:ℝ) ≤ 2*X ∧ X^2 ≤ (m:ℝ)^2*X^(2*s) ∧ (m:ℝ)^2*X^(2*s) ≤ 4*X^2
  rw [hw,← mul_pow]
  refine ⟨Nat.ceil_pos.mpr (zero_lt_one.trans_le hf),
    (le_mul_of_one_le_right (Nat.cast_nonneg _) hg).trans h₄,pow_le_pow_left₀ hx.le h₃ 2,?_⟩
  exact (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hg)) h₄ 2).trans_eq (by ring)

/-- Every subcritical strip has a single rational comparison per conductor.
The exponent of the integer base stays fixed while the multiplicity changes. -/
theorem zetaZeroWidth_le_iff_stripMultiplicity_power {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      ordinaryPrimeGenerator (stripMultiplicity s n • successorSquareTriple n) ≤ (B:ℚ)^((n+1)^2) := by
  obtain ⟨E,hE,he⟩ := successorSquare_degree_window_error
  rw [zetaZeroWidth_le_iff_successorSquareTriple hs hs']
  constructor
  · rintro ⟨A,hA⟩
    let B := ⌈Real.exp (E+4*|A|)⌉₊
    have hb : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
    have hbase : E+4*|A| ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hb)).mpr (Nat.le_ceil _)
    refine ⟨B,hb,fun n hn => (logPower _ hb (n+1)).mpr ?_⟩
    let m := stripMultiplicity s n
    obtain ⟨hm,hwin,_,hu⟩ := stripMultiplicity_bounds hs hs' n
    have hpow : 0 ≤ ((n:ℝ)+1)^(2*s) := Real.rpow_nonneg (by positivity) _
    have ha' := mul_le_mul_of_nonneg_right (le_abs_self A) hpow
    have hq := mul_le_mul_of_nonneg_left (hA n hn) (sq_nonneg (m:ℝ))
    have hq' := mul_le_mul_of_nonneg_left ha' (sq_nonneg (m:ℝ))
    have htop := mul_le_mul_of_nonneg_left hu (abs_nonneg A)
    have hh := (abs_le.mp (he hn hm hwin)).2
    push_cast
    linarith only [hq,hq',htop,hh,mul_le_mul_of_nonneg_right hbase (sq_nonneg ((n:ℝ)+1))]
  · rintro ⟨B,hB,h⟩
    have hlog := Real.log_nonneg (show (1:ℝ) ≤ B by exact_mod_cast hB)
    refine ⟨Real.log B+E,fun n hn => ?_⟩
    let m := stripMultiplicity s n
    obtain ⟨hm,hwin,hl,_⟩ := stripMultiplicity_bounds hs hs' n
    have hpos : 0 < (m:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hm)
    apply (mul_le_mul_iff_right₀ hpos).mp
    have hh := (abs_le.mp (he hn hm hwin)).1
    have hx := (logPower _ hB (n+1)).mp (h n hn)
    push_cast at hx
    linarith only [hh,hx,mul_le_mul_of_nonneg_left hl (add_nonneg hlog hE)]

/-- The established zero-free half-plane supplies a common integer base
at multiplicity growing to the power 15001/24000 of the conductor parameter. -/
theorem subThreeEighths_stripMultiplicity_power :
    ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      ordinaryPrimeGenerator (stripMultiplicity (8999/24000) n • successorSquareTriple n) ≤
        (B:ℚ)^((n+1)^2) :=
  (zetaZeroWidth_le_iff_stripMultiplicity_power (by norm_num) (by norm_num)).mp
    ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths

#print axioms ordinaryPrimeContact_sampling_error
#print axioms ordinaryPrimeContact_error
#print axioms riemannHypothesis_iff_diagonal_successorSquare_power
#print axioms successorSquare_log_negligible
#print axioms subThreeEighths_stripMultiplicity_power

end GaloisForLFunctions.CountingHolography.Sections
