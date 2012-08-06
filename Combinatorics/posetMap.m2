PosetMap = new Type of HashTable

posetMap(List):= PosetMap => L -> (     
	if all(L, #L ===2 ) and (sort apply(L, i-> first i) == sort P1.GroundSet) then
	(
		permutation hashTable apply(#M, i -> first M_i => last M_i)
	) else error "Not a map on posets."
)


posetMap(HashTable) := PosetMap => (H) -> 
	new PosetMap from hashTable {symbol map => H, symbol cache => new CacheTable}
	
	
new PosetMap from {
     symbol Source => P1,
     symbol Target => P2,
     symbol map => M
     
     }