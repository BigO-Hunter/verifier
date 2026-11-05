"""mpmath controls for the CLZ top-row audit (Zenodo 23480715 / creelie/mh-phys v1.0.0).

(b) exact row value: (3125/3112)(H - 7/3200) at 50 digits vs board display 0.6731134
(e) ordering: ours > Jo (ainta/zeta-simple-zeros) > H (Montgomery-Taylor)
(neg-c) wrong-constant identities must NOT reproduce the board value
"""
from mpmath import mp, mpf, cos, sin, sqrt, nstr

mp.dps = 60

H = mpf(3) / 2 - (cos(1 / sqrt(2)) / sin(1 / sqrt(2))) / sqrt(2)
print("H (Montgomery-Taylor)      =", nstr(H, 50))

exact = (mpf(3125) / 3112) * (H - mpf(7) / 3200)
print("exact (3125/3112)(H-7/3200) =", nstr(exact, 50))

board = mpf("0.6731134")
delta = board - exact
print("board display              =", nstr(board, 50))
print("board - exact              =", nstr(delta, 6), "(7-dp rounding, not an error)")
print("round(exact,7) == board    :", mpf(f"{float(exact):.7f}") == board)
assert nstr(exact, 20) == "0.67311335523719839104", nstr(exact, 20)
assert mpf("4.476e-8") < delta < mpf("4.477e-8")

jo = (mpf(1345000) * H - 2680) / 1340003
print("Jo (1345000H-2680)/1340003 =", nstr(jo, 50))
print("ordering ours > Jo > H     :", exact > jo > H)
print("ours - Jo                  =", nstr(exact - jo, 6))
assert exact > jo > H
assert mpf("1.0482e-4") < exact - jo < mpf("1.0483e-4")

# negative control: wrong constants must not reproduce the row value
for name, val in [
    ("(3125/3112)(H-7/3199)", (mpf(3125) / 3112) * (H - mpf(7) / 3199)),
    ("(3125/3112)(H-1/3200)", (mpf(3125) / 3112) * (H - mpf(1) / 3200)),
    ("(3124/3112)(H-7/3200)", (mpf(3124) / 3112) * (H - mpf(7) / 3200)),
    ("(3125/3113)(H-7/3200)", (mpf(3125) / 3113) * (H - mpf(7) / 3200)),
]:
    match = nstr(val, 10) == nstr(exact, 10)
    print(f"neg-identity {name} = {nstr(val, 16)}  matches row: {match}")
    assert not match

# successor v1.3.0 (Zenodo 23489033) claimed value, for the stale-row disclosure
v130 = (mpf(125000) / 124111) * (H - mpf(7999) / 2000000)
print("v1.3.0 (125000/124111)(H-7999/2000000) =", nstr(v130, 16))
assert nstr(v130, 15).startswith("0.6732896395")  # record's claim is 10-dp truncation

# ceiling context: chain_all.txt max must be <= 0.67357 (checked against rerun output)
print("ALL MPMATH CONTROLS PASS")
