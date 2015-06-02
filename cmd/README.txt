README

Chris Pac
Seattle Chord Assignment Documentation

All the files have an extension of .py for easy of coding in python editor. 
The .py extension does not seem to have any impact on running the script. 
All coding was done on Windows.

Synchronization timer is set to a random number between 7 and 12 sec. 
So, it takes the ring few min to fully stabilize. This was done to 
limit the number of UDP packets that are sent. (~6min for 10 nodes)

The command-line arguments have been changed for chord.py to 
accommodate the fact that: getmyip() function is used to get the 
ip address and only port number needs to be provided. 
The new command line arguments follow this format:
chord.py port timeout [seed_ip seed_port]

All other scripts follow the specified format:
get.py ip port key
put.py ip port key value
dump.py [optional filename] [default file: nodes.conf]

Extra features:
I've added chord_misc.py which provides some convenient ways to monitor and change the state of nodes.
chord_misc.py print [optional: filename] or [ip port]
chord_misc.py stop  [optional: filename] or [ip port]
chord_misc.py restart  [optional: filename] or [ip port]
chord_misc.py leave [optional: filename] or [ip port]
chord_misc.py phash [optional: filename] or [ip port]
chord_misc.py hello [optional: filename] or [ip port trace_lvl]
#default file: nodes.conf

print will cause one or more of the nodes to print its state.
stop will cause one or more of the nodes to stop synchronization (i.e. stabilize, fix fingers, check 										predecessor)
restart will cause one or more of the nodes start synchronization
leave will cause one or more of the nodes to leave the ring
phash will just do a quick print of the hash generated from the ip:port value
hello will cause one or more of the nodes to send 'hello back'

Search feature:
Please ignore the search functionality in the assignment. I've made a mistake of adding it 
before turning in this assignment, which just cause this assignment to be delayed.  Thank you 


BUGS:
1) There is a possible bug that could cause a key/value to not be transferred correctly to a joining node. 
The joining node acquires the values from its successor before it stabilizes. Thus there is a time window 
where the node has the values but has not yet fully joined the ring. If during that time the successor, 
of the joining node, gets a value that should belong to the joining node it will stay at the successor 
and the joining node will not get it.




