import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.WellFounded
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.StabilizedSpectra

/-! # Mutual and terminal classes realized at a common dilation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Finset Set

private theorem scale_up {s t : ℝ} {a b : ℕ} (h : Forces (s*a) (t*a)) (ab : a ∣ b) :
    Forces (s*b) (t*b) := by
  obtain ⟨k,rfl⟩ := ab
  simpa only [Nat.cast_mul,mul_assoc] using forces_dilate h k

/-- Two positive readings have the same least consequence set exactly when each forces the other. -/
theorem consequences_eq_iff_mutual {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    consequences x=consequences y ↔ Forces x y ∧ Forces y x := by
  constructor
  · intro eq
    have a : x ∈ consequences x := ⟨hx,fun _ _ h => h⟩
    have b : y ∈ consequences y := ⟨hy,fun _ _ h => h⟩
    rw [eq] at a
    rw [← eq] at b
    exact ⟨b.2,a.2⟩
  · rintro ⟨f,g⟩
    exact Set.Subset.antisymm
      (fun _ h => ⟨h.1,fun n a z => h.2 n a (g n a z)⟩)
      (fun _ h => ⟨h.1,fun n a z => h.2 n a (f n a z)⟩)

/-- The complete mutual class of any resonant source is the equality class
of a single attainable least spectrum at every multiple of a common scale. -/
theorem mutual_spectra {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k → Attainable (consequences (t*↑(M*k))) ∧
      ∀ u : ℝ, 0<u → (consequences (t*↑(M*k))=consequences (u*↑(M*k)) ↔ u ∈ mutualOrders t) := by
  classical
  letI : Fintype (mutualOrders t) := (finite_mutual ht res).fintype
  have forward (u : mutualOrders t) : ∃ a : ℕ, 0<a ∧ Forces (t*a) (u.val*a) := u.property.1.2
  have reverse (u : mutualOrders t) : ∃ b : ℕ, 0<b ∧ Forces (u.val*b) (t*b) := u.property.2.2
  choose a ap f using forward
  choose b bp g using reverse
  let M := ∏ u, a u*b u
  have mp : 0<M := prod_pos fun u _ => mul_pos (ap u) (bp u)
  refine ⟨M,mp,fun k kp => ?_⟩
  have p := mul_pos mp kp
  have pos : 0<(↑(M*k) : ℝ) := Nat.cast_pos.mpr p
  refine ⟨least_spectrum (mul_pos ht pos) ((resonant_nat_iff ht p).mpr res),fun u hu => ?_⟩
  rw [consequences_eq_iff_mutual (mul_pos ht pos) (mul_pos hu pos)]
  constructor
  · rintro ⟨h,j⟩
    exact ⟨⟨hu,M*k,p,h⟩,ht,M*k,p,j⟩
  · intro hit
    let v : mutualOrders t := ⟨u,hit⟩
    have dv : a v*b v ∣ M := dvd_prod_of_mem _ (mem_univ v)
    have d := dv.trans (dvd_mul_right M k)
    exact ⟨scale_up (f v) ((dvd_mul_right (a v) (b v)).trans d),
      scale_up (g v) ((dvd_mul_left (b v) (a v)).trans d)⟩

/-- A terminal consequence forces exactly its own finite equivalence class. -/
theorem exists_terminal {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ u ∈ accumulated t, Resonant u ∧ accumulated u=mutualOrders u ∧ (accumulated u).Finite := by
  classical
  let S := {x : ResonantOrder | x.val ∈ accumulated t}
  have self : S.Nonempty := ⟨⟨t,ht,res⟩,accumulated_self ht⟩
  obtain ⟨x,hit,minimal⟩ := strict_wellFounded.has_min S self
  have eq : accumulated x.val=mutualOrders x.val := by
    refine Set.Subset.antisymm ?_ (fun _ h => h.1)
    intro v forward
    refine ⟨forward,?_⟩
    by_contra missing
    let y : ResonantOrder := ⟨v,forward.1,resonant_of_accumulated x.property.1 x.property.2 forward⟩
    exact minimal y (accumulated_trans hit forward) ⟨forward,missing⟩
  refine ⟨x.val,hit,x.property.2,eq,?_⟩
  rw [eq]
  exact finite_mutual x.property.1 x.property.2

/-- At a terminal reading, one finite shell spectrum at each multiple of a
single dilation realizes exactly all mutually forcing normalized readings. -/
theorem terminal_spectra {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ u ∈ accumulated t, Resonant u ∧ accumulated u=mutualOrders u ∧
      ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k → ∃ S : Set ℝ,
        Attainable S ∧ u*↑(M*k) ∈ S ∧ ∀ v : ℝ, 0<v → (v*↑(M*k) ∈ S ↔ v ∈ mutualOrders u) := by
  obtain ⟨u,hit,rs,eq,fin⟩ := exists_terminal ht res
  obtain ⟨M,pos,realize⟩ := (finite_iff_stabilized hit.1).mp fin
  refine ⟨u,hit,rs,eq,M,pos,fun k hk => ?_⟩
  simpa only [← eq] using realize k hk

#print axioms mutual_spectra
#print axioms exists_terminal
#print axioms terminal_spectra

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
